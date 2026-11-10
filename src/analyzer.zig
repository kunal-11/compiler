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
                const eval = Eval.init(ctx, arena, symbol.file);
                const file = ctx.getFile(symbol.file);

                const res_type = if (symbol.type_inst != .none)
                    eval.evalInst(symbol.type_inst, ctx.type_pool.literal(.type_id)).value.val.type
                else
                    .none;
                const result = eval.evalInst(symbol.value_inst, res_type).value;

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
                lower.lowerInst(func.untyped_inst, func.type);
                const fn_inst = lower.results[@backingInt(func.untyped_inst)].inst;
                func.status = .{ .checked = fn_inst };
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
        if (inst_id == .none) return .none;
        if (inst_id == .poison) return .poison;
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

    fn lowerInst(lower: *Lower, inst_id: UntypedIr.InstId, res_type: Type.Id) void {
        const file = lower.ctx.getFile(lower.file_id);
        const inst = file.untyped_ir.getInst(inst_id);
        const res: Value = switch (inst.tag) {
            .fn_lit => blk: {
                const marker = lower.inst_count;
                for (0..inst.data.fn_lit.body.count) |inst_idx| {
                    const id = lower.untyped_ir.extras[inst.data.fn_lit.body.offset + inst_idx];
                    lower.lowerInst(id, .none);
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

            .store => blk: {
                const addr = lower.ref(inst.data.bin_op.lhs);
                const rhs = lower.ref(inst.data.bin_op.rhs);

                // TODO: coerce lhs to rhs pointer

                const typed_inst = lower.emit(.{
                    .type = lower.ctx.type_pool.literal(.void),
                    .pos = inst.pos,
                    .tag = .store,
                    .data = .{ .bin_op = .{ .lhs = addr, .rhs = rhs } },
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
                    .type = lower.ctx.type_pool.ptr(type_id),
                    .pos = inst.pos,
                    .tag = .alloc,
                    .data = .{ .alloc = type_id },
                });
                break :blk .{ .inst = typed_inst };
            },

            .add, .subtract, .mul, .div, .mod => blk: {
                const lhs = lower.results[@backingInt(inst.data.bin_op.lhs)];
                const rhs = lower.results[@backingInt(inst.data.bin_op.rhs)];
                if (lhs == .constant and rhs == .constant) {
                    const res = lower.eval.evalInst(inst_id, res_type);
                    lower.eval.results[@backingInt(inst_id)] = res.value;
                    break :blk .constant;
                } else {
                    const lhs_ref = lower.ref(inst.data.bin_op.lhs);
                    const rhs_ref = lower.ref(inst.data.bin_op.rhs);

                    const lhs_type = lower.typed_ir.getInst(lhs_ref).type;
                    const rhs_type = lower.typed_ir.getInst(rhs_ref).type;
                    const type_id = peerType(lower.ctx, lhs_type, rhs_type);
                    // if (type_id == .none) {
                    //     @panic("TODO: handle type check error");
                    // }

                    const typed_inst = lower.emit(.{
                        .pos = inst.pos,
                        .type = type_id,
                        .tag = switch (inst.tag) {
                            .add => .add,
                            .subtract => .subtract,
                            .mul => .mul,
                            .div => .div,
                            .mod => .mod,
                            else => unreachable,
                        },
                        .data = .{ .bin_op = .{ .lhs = lhs_ref, .rhs = rhs_ref } },
                    });
                    break :blk .{ .inst = typed_inst };
                }
            },

            .global_ptr, .global_val => @panic("TODO: global name resolve"),

            .ret, .ret_implicit => blk: {
                // TODO: remove ret_implicit based on coverage

                const val = lower.ref(inst.data.unary_op);
                const typed_inst = lower.emit(.{
                    .pos = inst.pos,
                    .tag = .ret,
                    .type = lower.ctx.type_pool.literal(.noreturn),
                    .data = .{ .unary_op = val },
                });
                break :blk .{ .inst = typed_inst };
            },

            .undef_lit, .type_lit, .num_lit, .bool_lit, .comp_block, .type_of, .fn_type => blk: {
                const res = lower.eval.evalInst(inst_id, res_type);
                lower.eval.results[@backingInt(inst_id)] = res.value;
                break :blk .constant;
            },

            else => @panic("TODO"),
        };
        lower.results[@backingInt(inst_id)] = res;

        const value_type = switch (res) {
            .none => unreachable,
            .constant => lower.eval.results[@backingInt(inst_id)].type,
            .inst => |i| lower.typed_ir.getInst(i).type,
        };

        if (!coerce(lower.ctx, value_type, res_type)) {
            @panic("TODO: handle type check error");
        }
    }
};

pub const Eval = struct {
    pub const Value = struct {
        type: Type.Id,
        val: union(enum) {
            void,
            undef,
            type: Type.Id,
            number: i64,
            boolean: bool,
            fn_lit: Func.Id,
        },
    };

    arena: *mem.Arena,
    results: []Value,

    ctx: *Context,
    file_id: File.Id,

    untyped_ir: *UntypedIr,
    namespace: *Namespace,

    pub fn init(ctx: *Context, arena: *mem.Arena, file_id: File.Id) *Eval {
        const file = ctx.getFile(file_id);
        const namespace = ctx.getNamespace(file.namespace_id);
        const eval = arena.pushStruct(Eval);
        eval.* = .{
            .arena = arena,
            .ctx = ctx,
            .file_id = file_id,
            .results = arena.pushArray(Value, file.untyped_ir.inst_count),
            .untyped_ir = file.untyped_ir,
            .namespace = namespace,
        };
        for (eval.results) |*r| r.* = .{ .type = .none, .val = .void };
        return eval;
    }

    pub const Result = struct {
        value: Value,
        control: union(enum) { none, brk: UntypedIr.InstId } = .none,
    };

    pub fn evalInst(eval: *Eval, inst_id: UntypedIr.InstId, res_type: Type.Id) Result {
        const file = eval.ctx.getFile(eval.file_id);
        const inst = file.untyped_ir.getInst(inst_id);
        const results = eval.results;
        const res: Result = switch (inst.tag) {
            .type_lit => .{ .value = .{
                .type = eval.ctx.type_pool.literal(.type_id),
                .val = .{ .type = eval.ctx.type_pool.literal(inst.data.type_lit) },
            } },
            .undef_lit => .{ .value = .{
                .type = eval.ctx.type_pool.literal(.comp_undef),
                .val = .undef,
            } },
            .num_lit => blk: {
                const num_token = lexer.lexToken(file.contents, inst.pos);
                debug.assert(num_token.tag == .num_literal, "num lit lexed token invalid");
                const num_str = file.contents[num_token.start..num_token.end];
                const num = math.parseInt(i64, num_str) catch @panic("TODO: handle invalid num");
                break :blk .{ .value = .{
                    .type = eval.ctx.type_pool.literal(.comp_int),
                    .val = .{ .number = num },
                } };
            },
            .bool_lit => .{ .value = .{
                .type = eval.ctx.type_pool.literal(.bool),
                .val = .{ .boolean = inst.data.bool_lit },
            } },

            .block, .comp_block => blk: {
                for (0..inst.data.block.count) |inst_idx| {
                    const child_id = file.untyped_ir.extras[inst.data.block.offset + inst_idx];
                    const res = eval.evalInst(child_id, .none);
                    switch (res.control) {
                        .none => eval.results[@backingInt(child_id)] = res.value,
                        .brk => |block| {
                            break :blk if (block == inst_id) .{ .value = res.value } else res;
                        },
                    }
                }
                @panic("block did not end with break");
            },

            .type_of => .{ .value = .{
                .type = eval.ctx.type_pool.literal(.type_id),
                .val = .{ .type = results[@backingInt(inst.data.unary_op)].type },
            } },

            .brk => .{
                .value = eval.results[@backingInt(inst.data.bin_op.rhs)],
                .control = .{ .brk = inst.data.bin_op.lhs },
            },

            .brk_implicit => .{
                .value = .{ .type = eval.ctx.type_pool.literal(.void), .val = .void },
                .control = .{ .brk = inst.data.unary_op },
            },

            .fn_type => blk: {
                const ret = results[@backingInt(inst.data.fn_type.return_type)].val.type;
                const args = eval.arena.pushArray(Type.Id, inst.data.fn_type.arg_types.count);
                for (0..inst.data.fn_type.arg_types.count) |i| {
                    const arg = file.untyped_ir.extras[inst.data.fn_type.arg_types.offset + i];
                    args[i] = results[@backingInt(arg)].val.type;
                }

                break :blk .{ .value = .{
                    .type = eval.ctx.type_pool.literal(.type_id),
                    .val = .{ .type = eval.ctx.type_pool.func(ret, args) },
                } };
            },
            .fn_lit => blk: {
                const type_res = results[@backingInt(inst.data.fn_lit.type)];
                const func_id = eval.ctx.func_table.add(.{
                    .file = eval.file_id,
                    .type = type_res.val.type,
                    .untyped_inst = inst_id,
                    .status = .unchecked,
                });
                break :blk .{ .value = .{
                    .type = type_res.val.type,
                    .val = .{ .fn_lit = func_id },
                } };
            },

            else => @panic("TODO: eval other instructions"),
        };

        if (!coerce(eval.ctx, res.value.type, res_type)) {
            @panic("TODO: handle type check error");
        }
        return res;
    }
};

fn coerce(ctx: *Context, from_id: Type.Id, to_id: Type.Id) bool {
    if (to_id == .none or from_id == to_id) return true;

    const from = ctx.type_pool.getType(from_id);
    if (from.tag == .lit) {
        const from_lit = from.data.lit;
        if (from_lit == .comp_undef) return true;

        // TODO: allow comp int to coerce if value is in bounds
    }
    return false;
}

fn peerType(ctx: *Context, t1: Type.Id, t2: Type.Id) Type.Id {
    _ = ctx;
    if (t1 == t2) return t1;
    return .none;
}
