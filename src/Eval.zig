const stdx = @import("stdx.zig");
const mem = stdx.mem;
const debug = stdx.debug;
const math = stdx.math;

const Context = @import("types.zig").Context;
const Type = @import("types.zig").Type;
const Func = @import("types.zig").Func;
const File = @import("types.zig").File;
const Namespace = @import("types.zig").Namespace;

const UntypedIr = @import("types.zig").UntypedIr;
const TypedIr = @import("types.zig").TypedIr;

const lexer = @import("lexer.zig");
const Eval = @This();

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

arena: mem.Arena,
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
        .arena = arena.subArena(8 * mem.KB),
        .ctx = ctx,
        .file_id = file_id,
        .results = arena.pushArray(Value, file.untyped_ir.inst_count),
        .untyped_ir = file.untyped_ir,
        .namespace = namespace,
    };
    for (eval.results) |*r| r.* = .{ .type = .none, .val = .void };
    return eval;
}

pub const Result = union(enum) {
    value: Value,
    brk: struct { val: Value, block: UntypedIr.InstId },
};

pub fn evalInst(eval: *Eval, inst_id: UntypedIr.InstId) Result {
    const file = eval.ctx.getFile(eval.file_id);
    const inst = file.untyped_ir.getInst(inst_id);
    const results = eval.results;
    return switch (inst.tag) {
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
                const res = eval.evalInst(child_id);
                switch (res) {
                    .value => |val| eval.results[@backingInt(child_id)] = val,
                    .brk => |brk| {
                        break :blk if (brk.block == inst_id) .{ .value = brk.val } else res;
                    },
                }
            }
            @panic("block did not end with break");
        },

        .type_of => .{ .value = .{
            .type = eval.ctx.type_pool.literal(.type_id),
            .val = .{ .type = results[@backingInt(inst.data.unary_op)].type },
        } },

        .brk => .{ .brk = .{
            .val = eval.results[@backingInt(inst.data.bin_op.rhs)],
            .block = inst.data.bin_op.lhs,
        } },

        .brk_implicit => .{ .brk = .{
            .val = .{ .type = eval.ctx.type_pool.literal(.void), .val = .void },
            .block = inst.data.unary_op,
        } },

        .fn_type => blk: {
            const flusher = mem.Flusher.init(&eval.arena);
            defer flusher.flush();

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
}
