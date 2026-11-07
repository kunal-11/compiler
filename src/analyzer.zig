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
                if (symbol.type_inst != .none) {
                    @panic("TODO: handle type annotations of global decls");
                }
                const file = ctx.getFile(symbol.file);

                const frame = EvalFrame.init(arena, file.untyped_ir.inst_count);
                const result = evalCompBlock(ctx, arena, symbol.file, symbol.value_inst, frame);

                switch (result.val) {
                    .fn_lit => {
                        const func = ctx.func_table.get(result.val.fn_lit);
                        if (func.status == .unchecked) {
                            ctx.analysis_q.push(.{ .fn_lit = result.val.fn_lit });
                            func.status = .{ .queued = frame };
                        }
                    },
                    else => {},
                }
                symbol.result = result;

                const name_token = lexer.lexToken(file.contents, symbol.pos);
                const name_str = file.contents[name_token.start..name_token.end];
                debug.log("analyzed value: {s} = {}", .{ name_str, result });
            },
            .fn_lit => |lit| {
                const func = ctx.func_table.get(lit);
                debug.assert(func.status == .queued, "fn check item invalid status");
                const typed_inst = lowerFnLit(
                    ctx,
                    arena,
                    func.file,
                    func.untyped_inst,
                    func.status.queued,
                );
                func.status = .{ .checked = typed_inst };
            },
            .empty => unreachable,
        }
    }
}

pub const Value = struct {
    type: Type.Id,
    val: union(enum) {
        none,
        undef,
        type: Type.Id,
        number: i64,
        boolean: bool,
        fn_lit: Func.Id,
    },
};

pub const EvalFrame = struct {
    results: []Value,

    pub fn init(arena: *mem.Arena, result_len: usize) *EvalFrame {
        const frame = arena.pushStruct(EvalFrame);
        frame.* = .{
            .results = arena.pushArray(Value, result_len),
        };
        for (frame.results) |*r| r.* = .{ .type = .none, .val = .none };
        return frame;
    }
};

fn lowerFnLit(
    ctx: *Context,
    arena: *mem.Arena,
    file_id: File.Id,
    lit_id: UntypedIr.InstId,
    frame: *EvalFrame,
) TypedIr.InstId {
    const file = ctx.getFile(file_id);

    const lit = file.untyped_ir.getInst(lit_id);
    debug.assert(lit.tag == .fn_lit, "lower not a fn lit");

    for (0..lit.data.fn_lit.body.count) |inst_idx| {
        const inst_id = file.untyped_ir.extras[lit.data.fn_lit.body.offset + inst_idx];
        const res = evaluateInst(ctx, arena, file_id, frame, inst_id, .emit);
        switch (res) {
            .brk => return .none,
            else => {},
        }
    }

    @panic("TODO");
}

fn evalCompBlock(
    ctx: *Context,
    arena: *mem.Arena,
    file_id: File.Id,
    block_id: UntypedIr.InstId,
    frame: *EvalFrame,
) Value {
    const file = ctx.getFile(file_id);
    const block = file.untyped_ir.getInst(block_id);
    debug.assert(block.tag == .comp_block, "evaluate not a comp block");

    for (0..block.data.block.count) |inst_idx| {
        const inst_id = file.untyped_ir.extras[block.data.block.offset + inst_idx];
        const res = evaluateInst(ctx, arena, file_id, frame, inst_id, .execute);
        switch (res) {
            .value => |val| frame.results[@backingInt(inst_id)] = val,
            // TODO: handle multi level breaks
            .brk => |brk| return frame.results[@backingInt(brk.val)],
            .ret => @panic("TODO"),
        }
    }
    @panic("Eval: block did not break");
}

const EvalResult = union(enum) {
    value: Value,
    ret: struct { val: UntypedIr.InstId },
    brk: struct { val: UntypedIr.InstId, block: UntypedIr.InstId },
};

fn evaluateInst(
    ctx: *Context,
    arena: *mem.Arena,
    file_id: File.Id,
    frame: *EvalFrame,
    inst_id: UntypedIr.InstId,
    mode: enum { emit, execute },
) EvalResult {
    _ = mode;
    const file = ctx.getFile(file_id);
    const inst = file.untyped_ir.getInst(inst_id);
    const results = frame.results;
    return switch (inst.tag) {
        .type_lit => .{ .value = .{
            .type = getTypeId(ctx, .type_id),
            .val = .{ .type = getTypeId(ctx, inst.data.type_lit) },
        } },
        .undef_lit => .{ .value = .{
            .type = getTypeId(ctx, .comp_undef),
            .val = .undef,
        } },
        .num_lit => blk: {
            const num_token = lexer.lexToken(file.contents, inst.pos);
            debug.assert(num_token.tag == .num_literal, "num lit lexed token invalid");
            const num_str = file.contents[num_token.start..num_token.end];
            const num = math.parseInt(i64, num_str) catch @panic("TODO: handle invalid num");
            break :blk .{ .value = .{
                .type = getTypeId(ctx, .comp_int),
                .val = .{ .number = num },
            } };
        },
        .bool_lit => .{ .value = .{
            .type = getTypeId(ctx, .bool),
            .val = .{ .boolean = inst.data.bool_lit },
        } },

        .type_of => .{ .value = .{
            .type = getTypeId(ctx, .type_id),
            .val = .{ .type = results[@backingInt(inst.data.unary_op)].type },
        } },

        .alloc, .load, .store => @panic("TODO: runtime instructions"),

        .global_val, .global_ptr => @panic("TODO: global name resolve"),

        .brk => blk: {
            break :blk .{ .brk = .{
                .val = inst.data.bin_op.rhs,
                .block = inst.data.bin_op.lhs,
            } };
        },

        .fn_type => blk: {
            const flusher = mem.Flusher.init(arena);
            defer flusher.flush();

            const ret = results[@backingInt(inst.data.fn_type.return_type)].val.type;
            const args = arena.pushArray(Type.Id, inst.data.fn_type.arg_types.count);
            for (0..inst.data.fn_type.arg_types.count) |i| {
                const arg = file.untyped_ir.extras[inst.data.fn_type.arg_types.offset + i];
                args[i] = results[@backingInt(arg)].val.type;
            }

            const constant_id = ctx.type_pool.getOrCreateId(.{
                .tag = .func,
                .data = .{ .func = .{ .ret = ret, .args = ctx.type_pool.allocList(args) } },
            });
            break :blk .{ .value = .{
                .type = getTypeId(ctx, .type_id),
                .val = .{ .type = constant_id },
            } };
        },
        .fn_lit => blk: {
            const type_res = results[@backingInt(inst.data.fn_lit.type)];
            const func_id = ctx.func_table.add(.{
                .file = file_id,
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
}

fn getTypeId(ctx: *Context, lit: TypeLit) Type.Id {
    return ctx.type_pool.getOrCreateId(.{
        .tag = .lit,
        .data = .{ .lit = lit },
    });
}
