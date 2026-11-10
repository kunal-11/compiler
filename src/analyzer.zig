const stdx = @import("stdx.zig");
const mem = stdx.mem;
const debug = stdx.debug;
const math = stdx.math;

const Context = @import("types.zig").Context;
const UntypedIr = @import("types.zig").UntypedIr;
const TypedIr = @import("types.zig").TypedIr;
const File = @import("types.zig").File;
const TypeLit = @import("types.zig").TypeLit;
const Symbol = @import("types.zig").Symbol;
const Type = @import("types.zig").Type;
const Func = @import("types.zig").Func;
const Namespace = @import("types.zig").Namespace;
const Constant = @import("types.zig").Constant;

const lexer = @import("lexer.zig");
const Eval = @import("Eval.zig");

pub const Queue = struct {
    pub const Item = union(enum) {
        empty,
        decl: Symbol.Id,
        fn_lit: Func.Id,
    };

    const len = 1024;

    items: [len]Item = undefined,
    read: u32 = 0,
    write: u32 = 1,

    pub fn push(q: *Queue, item: Item) void {
        debug.assert((q.write + 1) % len != q.read, "analysis queue OOM");
        q.items[q.write] = item;
        q.write = (q.write + 1) % len;
    }

    pub fn pop(q: *Queue) Item {
        if ((q.read + 1) % len == q.write) return .empty;
        q.read = (q.read + 1) % len;
        return q.items[q.read];
    }
};

pub fn analyze(ctx: *Context, arena: *mem.Arena) void {
    const flusher = mem.Flusher.init(arena);
    defer flusher.flush();

    var item = ctx.analysis_q.pop();
    while (item != .empty) : (item = ctx.analysis_q.pop()) {
        switch (item) {
            .decl => |decl| {
                const symbol = ctx.symbol_table.get(decl);
                if (symbol.type_inst != .none) {
                    @panic("TODO: handle type annotations of global decls");
                }
                const file = ctx.getFile(symbol.file);

                const eval = Eval.init(ctx, arena, symbol.file);
                const result = eval.evalInst(symbol.value_inst).value;

                switch (result.val) {
                    .fn_lit => {
                        const func = ctx.func_table.get(result.val.fn_lit);
                        if (func.status == .unchecked) {
                            ctx.analysis_q.push(.{ .fn_lit = result.val.fn_lit });
                            func.status = .{ .queued = eval };
                        }
                    },
                    else => {},
                }

                const name_token = lexer.lexToken(file.contents, symbol.pos);
                const name_str = file.contents[name_token.start..name_token.end];
                debug.log("analyzed value: {s} = {}", .{ name_str, result });
            },
            .fn_lit => |lit| {
                const func = ctx.func_table.get(lit);
                debug.assert(func.status == .queued, "fn check item invalid status");

                const lower = Lower.init(ctx, func.file, func.status.queued, arena);
                lower.lowerInst(func.untyped_inst);
                func.status = .{ .checked = lower.results[@backingInt(func.untyped_inst)].inst };
            },
            .empty => unreachable,
        }
    }
}

const Lower = struct {
    const Value = union(enum) {
        none,
        constant,
        inst: TypedIr.InstId,
    };

    ctx: *Context,
    file_id: File.Id,

    untyped_ir: *UntypedIr,
    typed_ir: *TypedIr,
    namespace: *Namespace,
    eval: *Eval,

    results: []Value,

    insts: [max_insts]TypedIr.InstId = undefined,
    inst_count: u32 = 0,

    const max_insts = 2048;

    pub fn init(ctx: *Context, file_id: File.Id, eval: *Eval, arena: *mem.Arena) *Lower {
        const lower = arena.pushStruct(Lower);
        const file = ctx.getFile(file_id);
        const ns = ctx.getNamespace(file.namespace_id);
        lower.* = .{
            .ctx = ctx,
            .file_id = file_id,
            .eval = eval,
            .namespace = ns,
            .typed_ir = file.typed_ir,
            .untyped_ir = file.untyped_ir,
            .results = arena.pushArray(Value, file.untyped_ir.inst_count),
        };
        for (lower.results) |*r| r.* = .none;
        return lower;
    }

    pub fn emit(lower: *Lower, inst: TypedIr.Inst) TypedIr.InstId {
        const inst_id = lower.typed_ir.allocInst(inst);
        lower.insts[lower.inst_count] = inst_id;
        lower.inst_count += 1;
        return inst_id;
    }

    fn ref(lower: *Lower, inst_id: UntypedIr.InstId) TypedIr.InstId {
        return switch (lower.results[@backingInt(inst_id)]) {
            .constant => blk: {
                const value = lower.eval.results[@backingInt(inst_id)];
                const const_id = switch (value.val) {
                    .undef => lower.ctx.constant_pool.undef(),
                    .number => lower.ctx.constant_pool.int(value.val.number),
                    .boolean => lower.ctx.constant_pool.boolean(value.val.boolean),
                    else => @panic("emit invalid constant"),
                };

                // TODO: fill position or make constants immediate
                break :blk lower.emit(.{
                    .type = value.type,
                    .pos = 0,
                    .tag = .constant,
                    .data = .{ .constant = const_id },
                });
            },
            .inst => |i| i,
            .none => @panic("invalid ref for none inst"),
        };
    }

    fn lowerInst(lower: *Lower, inst_id: UntypedIr.InstId) void {
        const file = lower.ctx.getFile(lower.file_id);
        const inst = file.untyped_ir.getInst(inst_id);
        lower.results[@backingInt(inst_id)] = switch (inst.tag) {
            .store => blk: {
                const addr = lower.ref(inst.data.bin_op.lhs);
                const rhs = lower.ref(inst.data.bin_op.rhs);

                // TODO: check lhs is pointer to type compatible with rhs

                const typed_inst = lower.emit(.{
                    .type = lower.ctx.type_pool.literal(.void),
                    .pos = inst.pos,
                    .tag = .store,
                    .data = .{ .bin_op = .{ .lhs = addr, .rhs = rhs } },
                });
                break :blk .{ .inst = typed_inst };
            },

            .fn_lit => blk: {
                const marker = lower.inst_count;
                for (0..inst.data.fn_lit.body.count) |inst_idx| {
                    const id = lower.untyped_ir.extras[inst.data.fn_lit.body.offset + inst_idx];
                    lowerInst(lower, id);
                }
                const block = lower.insts[marker..lower.inst_count];
                lower.inst_count = marker;

                const typed_inst = lower.emit(.{
                    .pos = inst.pos,
                    .type = lower.eval.results[@backingInt(inst_id)].type,
                    .tag = .func,
                    .data = .{ .block = lower.typed_ir.allocList(block) },
                });
                break :blk .{ .inst = typed_inst };
            },

            .load => blk: {
                const addr = lower.ref(inst.data.unary_op);
                const addr_inst = lower.typed_ir.getInst(addr);
                const typed_inst = lower.emit(.{
                    .type = lower.ctx.type_pool.getType(addr_inst.type).data.ptr,
                    .pos = inst.pos,
                    .tag = .load,
                    .data = .{ .unary_op = addr },
                });
                break :blk .{ .inst = typed_inst };
            },

            .alloc => blk: {
                const type_id = lower.eval.results[@backingInt(inst.data.unary_op)].val.type;
                const typed_inst = lower.emit(.{
                    .type = type_id,
                    .pos = inst.pos,
                    .tag = .alloc,
                    .data = .{ .alloc = type_id },
                });
                break :blk .{ .inst = typed_inst };
            },

            .add => @panic("TODO: arithmatic"),

            .global_ptr, .global_val => @panic("TODO: global name resolve"),

            .ret, .ret_implicit => @panic("TODO: ret"),

            .undef_lit, .type_lit, .num_lit, .bool_lit, .comp_block, .type_of, .fn_type => blk: {
                const res = lower.eval.evalInst(inst_id);
                lower.eval.results[@backingInt(inst_id)] = res.value;
                break :blk .constant;
            },

            else => @panic("TODO"),
        };
    }
};
