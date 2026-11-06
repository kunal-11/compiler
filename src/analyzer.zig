const stdx = @import("stdx.zig");
const mem = stdx.mem;
const debug = stdx.debug;
const math = stdx.math;

const Context = @import("types.zig").Context;
const UntypedIr = @import("types.zig").UntypedIr;
const TypedIr = @import("types.zig").TypedIr;
const File = @import("types.zig").File;
const TypeLit = @import("types.zig").TypeLit;
const Constant = @import("types.zig").Constant;
const Symbol = @import("types.zig").Symbol;

const lexer = @import("lexer.zig");

pub const Queue = struct {
    pub const Item = union(enum) {
        empty,
        decl: struct {
            file: File.Id,
            symbol: Symbol.Id,
        },
        fn_lit: Constant.Id,
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
    type: Constant.Id,
    val: union(enum) {
        type: Constant.Id,
        number: i64,
        boolean: bool,
        undef: void,
        fn_lit: Constant.Id,
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

                const result_id = evaluate(ctx, arena, symbol.file, symbol.value_inst);
                const file = ctx.getFile(decl.file);
                const result = file.analysis[@backingInt(result_id)];

                switch (result.val) {
                    .fn_lit => {
                        const entry = ctx.constants.getSideEntry(result.val.fn_lit);
                        if (entry.fn_lit == .unchecked) {
                            ctx.analysis_q.push(.{ .fn_lit = result.val.fn_lit });
                            entry.* = .{ .fn_lit = .queued };
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
                const data = ctx.constants.get(lit);
                debug.assert(
                    ctx.constants.getSideEntry(lit).fn_lit == .queued,
                    "fn check item invalid status",
                );
                const typed_inst = typeCheckFn(ctx, data.data.fn_lit.file, data.data.fn_lit.inst);
                ctx.constants.getSideEntry(lit).* = .{ .fn_lit = .{ .checked = typed_inst } };
            },
            .empty => unreachable,
        }
    }
}

fn evaluate(
    ctx: *Context,
    arena: *mem.Arena,
    file_id: File.Id,
    block_id: UntypedIr.InstId,
) UntypedIr.InstId {
    const file = ctx.getFile(file_id);

    if (file.analysis.len == 0) {
        file.analysis = file.arena.pushArray(Value, file.untyped_ir.inst_count);
        // just for safety check ?
        for (file.analysis) |*r| r.* = .{ .type = .none, .val = undefined };
    }
    const results = file.analysis;

    const block = file.untyped_ir.getInst(block_id);
    debug.assert(block.tag == .comp_block, "evaluate not a comp block");

    for (block.data.block) |inst_id| {
        const inst = file.untyped_ir.getInst(inst_id);
        results[@backingInt(inst_id)] = switch (inst.tag) {
            .type_lit => blk: {
                break :blk .{
                    .type = getTypeId(ctx, .type_id),
                    .val = .{ .type = getTypeId(ctx, inst.data.type_lit) },
                };
            },
            .fn_type => blk: {
                const flusher1 = mem.Flusher.init(arena);
                defer flusher1.flush();

                const ret = results[@backingInt(inst.data.fn_type.return_type)].val.type;
                const args = arena.pushArray(Constant.Id, inst.data.fn_type.arg_types.len);
                for (inst.data.fn_type.arg_types, 0..) |arg, i| {
                    args[i] = results[@backingInt(arg)].val.type;
                }

                const constant_id = ctx.constants.getOrAddId(.{
                    .tag = .fn_type,
                    .data = .{ .fn_type = .{ .ret = ret, .args = args } },
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
            .brk => return inst.data.bin_op.rhs,

            .fn_lit => blk: {
                const type_res = file.analysis[@backingInt(inst.data.fn_lit.type)];
                break :blk .{
                    .type = type_res.val.type,
                    .val = .{ .fn_lit = addFnLitConstant(ctx, file_id, inst_id) },
                };
            },

            else => @panic("TODO: eval other instructions"),
        };
    }

    @panic("Eval: compile block did not break");
}

fn addFnLitConstant(ctx: *Context, file: File.Id, inst: UntypedIr.InstId) Constant.Id {
    const const_id = ctx.constants.getOrAddId(.{
        .tag = .fn_lit,
        .data = .{ .fn_lit = .{ .file = file, .inst = inst } },
    });
    const entry = ctx.constants.getSideEntry(const_id);
    if (entry.* == .empty) {
        entry.* = .{ .fn_lit = .unchecked };
    }
    return const_id;
}

fn getTypeId(ctx: *Context, lit: TypeLit) Constant.Id {
    return ctx.constants.getOrAddId(.{
        .tag = .type_lit,
        .data = .{ .type_lit = lit },
    });
}

fn typeCheckFn(ctx: *Context, file_id: File.Id, inst_id: UntypedIr.InstId) TypedIr.InstId {
    const file = ctx.getFile(file_id);
    const lit = file.untyped_ir.getInst(inst_id).data.fn_lit;

    const type_id = file.analysis[@backingInt(lit.type)].val.type;
    const type_val = ctx.constants.get(type_id);
    debug.assert(type_val.tag == .fn_type, "fn type invalid");

    debug.log("type checking fn with type: {}", .{type_val.data.fn_type});
    for (lit.body) |inst| {
        _ = inst;
    }
    return .none;
}
