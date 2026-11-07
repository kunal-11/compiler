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
        decl: struct {
            file: File.Id,
            symbol: Symbol.Id,
        },
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

pub const Value = struct {
    type: Type.Id,
    val: union(enum) {
        type: Type.Id,
        number: i64,
        boolean: bool,
        undef: void,
        fn_lit: Func.Id,
    },
};

pub fn analyze(ctx: *Context, arena: *mem.Arena) void {
    var item = ctx.analysis_q.pop();
    while (item != .empty) : (item = ctx.analysis_q.pop()) {
        switch (item) {
            .decl => |decl| {
                const symbol = ctx.symbol_table.get(decl.symbol);
                if (symbol.type_inst != .none) {
                    @panic("TODO: handle type annotations of global decls");
                }

                const result = evalCompBlock(ctx, arena, symbol.file, symbol.value_inst);
                const file = ctx.getFile(decl.file);

                switch (result.val) {
                    .fn_lit => {
                        const func = ctx.func_table.get(result.val.fn_lit);
                        if (func.status == .unchecked) {
                            ctx.analysis_q.push(.{ .fn_lit = result.val.fn_lit });
                            func.status = .queued;
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
                    &.{},
                );
                func.status = .checked;
                func.typed_inst = typed_inst;
            },
            .empty => unreachable,
        }
    }
}

fn lowerFnLit(
    ctx: *Context,
    arena: *mem.Arena,
    file_id: File.Id,
    lit_id: UntypedIr.InstId,
    results: []Value,
) TypedIr.InstId {
    const file = ctx.getFile(file_id);

    const lit = file.untyped_ir.getInst(lit_id);
    debug.assert(lit.tag == .fn_lit, "lower not a fn lit");

    for (0..lit.data.fn_lit.body.count) |inst_idx| {
        const inst_id = file.untyped_ir.extras[lit.data.fn_lit.body.offset + inst_idx];
        const res = evaluateInst(ctx, arena, file_id, results, inst_id, .execute);
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
) Value {
    const file = ctx.getFile(file_id);

    const results = arena.pushArray(Value, file.untyped_ir.inst_count);
    // just for safety check
    for (results) |*r| r.* = .{ .type = .none, .val = undefined };

    const block = file.untyped_ir.getInst(block_id);
    debug.assert(block.tag == .comp_block, "evaluate not a comp block");

    for (0..block.data.block.count) |inst_idx| {
        const inst_id = file.untyped_ir.extras[block.data.block.offset + inst_idx];
        const res = evaluateInst(ctx, arena, file_id, results, inst_id, .execute);
        switch (res) {
            .brk => return results[@backingInt(inst_id)],
            else => {},
        }
    }

    @panic("Eval: block did not break");
}

const EvalResult = enum { success, brk };

fn evaluateInst(
    ctx: *Context,
    arena: *mem.Arena,
    file_id: File.Id,
    results: []Value,
    inst_id: UntypedIr.InstId,
    mode: enum { emit, execute },
) EvalResult {
    _ = mode;
    const file = ctx.getFile(file_id);
    const inst = file.untyped_ir.getInst(inst_id);
    var result = EvalResult.success;

    results[@backingInt(inst_id)] = switch (inst.tag) {
        .type_lit => blk: {
            break :blk .{
                .type = getTypeId(ctx, .type_id),
                .val = .{ .type = getTypeId(ctx, inst.data.type_lit) },
            };
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
            break :blk .{
                .type = getTypeId(ctx, .type_id),
                .val = .{ .type = constant_id },
            };
        },
        .num_lit => blk: {
            const num_token = lexer.lexToken(file.contents, inst.pos);
            debug.assert(num_token.tag == .num_literal, "num lit lexed token invalid");
            const num_str = file.contents[num_token.start..num_token.end];
            const num = math.parseInt(i64, num_str) catch @panic("TODO: handle invalid num");
            break :blk .{
                .type = getTypeId(ctx, .comp_int),
                .val = .{ .number = num },
            };
        },
        .brk => blk: {
            result = .brk;
            break :blk results[@backingInt(inst.data.bin_op.rhs)];
        },

        .fn_lit => blk: {
            const type_res = results[@backingInt(inst.data.fn_lit.type)];
            const func_id = ctx.func_table.add(.{
                .file = file_id,
                .status = .unchecked,
                .type = type_res.val.type,
                .untyped_inst = inst_id,
                .typed_inst = .none,
            });
            break :blk .{
                .type = type_res.val.type,
                .val = .{ .fn_lit = func_id },
            };
        },

        else => @panic("TODO: eval other instructions"),
    };
    return result;
}

fn getTypeId(ctx: *Context, lit: TypeLit) Type.Id {
    return ctx.type_pool.getOrCreateId(.{
        .tag = .lit,
        .data = .{ .lit = lit },
    });
}
