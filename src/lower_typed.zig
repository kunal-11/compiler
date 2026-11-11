const stdx = @import("stdx.zig");
const mem = stdx.mem;
const debug = stdx.debug;
const math = stdx.math;

const Context = @import("types.zig").Context;
const File = @import("types.zig").File;
const Type = @import("types.zig").Type;
const Func = @import("types.zig").Func;
const Namespace = @import("types.zig").Namespace;

const TypedIr = @import("types.zig").TypedIr;
const UntypedIr = @import("types.zig").UntypedIr;

const lexer = @import("lexer.zig");

pub const Known = struct {
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

const Value = union(enum) {
    none,
    known: Known,
    runtime: TypedIr.InstId,
};

pub const State = struct {
    arena: *mem.Arena,

    ctx: *Context,
    file_id: File.Id,

    untyped_ir: *UntypedIr,
    typed_ir: *TypedIr,
    namespace: *Namespace,

    results: []Value,

    insts: [max_insts]TypedIr.InstId = undefined,
    inst_count: u32 = 0,

    const max_insts = 2048;

    pub fn init(ctx: *Context, file_id: File.Id, arena: *mem.Arena) *State {
        const lower = arena.pushStruct(State);
        const file = ctx.getFile(file_id);
        const ns = ctx.getNamespace(file.namespace_id);
        lower.* = .{
            .arena = arena,
            .ctx = ctx,
            .file_id = file_id,
            .namespace = ns,
            .typed_ir = file.typed_ir,
            .untyped_ir = file.untyped_ir,
            .results = arena.pushArray(Value, file.untyped_ir.inst_count),
        };
        for (lower.results) |*r| r.* = .none;
        return lower;
    }

    pub fn emit(lower: *State, inst: TypedIr.Inst) TypedIr.InstId {
        const inst_id = lower.typed_ir.allocInst(inst);
        lower.insts[lower.inst_count] = inst_id;
        lower.inst_count += 1;
        return inst_id;
    }

    fn typeOf(lower: *State, inst_id: UntypedIr.InstId) Type.Id {
        return switch (lower.results[@backingInt(inst_id)]) {
            .none => @panic("type of none value"),
            .known => |val| val.type,
            .runtime => |child_id| rt_blk: {
                const child = lower.typed_ir.getInst(child_id);
                break :rt_blk child.type;
            },
        };
    }

    fn ref(lower: *State, inst_id: UntypedIr.InstId) TypedIr.InstId {
        if (inst_id == .none) return .none;
        return switch (lower.results[@backingInt(inst_id)]) {
            .known => |value| blk: {
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
            .runtime => |i| i,
            .none => @panic("invalid ref for none inst"),
        };
    }
};

pub const ResultType = union(enum) { implicit, explicit: Type.Id };

pub fn evalBlock(
    ctx: *Context,
    arena: *mem.Arena,
    file_id: File.Id,
    inst_id: UntypedIr.InstId,
    res_type: ResultType,
) *State {
    const state = State.init(ctx, file_id, arena);
    const jump = lowerInst(state, inst_id, res_type, .exec);
    debug.assert(jump == .none, "global block must break to itself");
    return state;
}

const Mode = enum { emit, exec };
const Jump = union(enum) {
    none,
    brk: struct { block: UntypedIr.InstId, value: Known },
};

pub fn lowerInst(lower: *State, inst_id: UntypedIr.InstId, res_type: ResultType, mode: Mode) Jump {
    const file = lower.ctx.getFile(lower.file_id);
    const inst = file.untyped_ir.getInst(inst_id);
    lower.results[@backingInt(inst_id)] = switch (inst.tag) {
        .comp_block => switch (mode) {
            .emit => blk: {
                const jump = lowerInst(lower, inst_id, res_type, .exec);
                debug.assert(jump == .none, "comp block cannot break in emit");
                break :blk lower.results[@backingInt(inst_id)];
            },
            .exec => blk: {
                for (0..inst.data.block.count) |inst_idx| {
                    const child_id = lower.untyped_ir.extras[inst.data.block.offset + inst_idx];
                    const jump = lowerInst(lower, child_id, res_type, .exec);
                    switch (jump) {
                        .none => {},
                        .brk => |res| if (res.block == inst_id)
                            break :blk .{ .known = res.value }
                        else
                            return jump,
                    }
                }
                @panic("block did not end with break");
            },
        },

        .fn_lit => switch (mode) {
            .emit => blk: {
                const marker = lower.inst_count;
                for (0..inst.data.fn_lit.body.count) |inst_idx| {
                    const id = lower.untyped_ir.extras[inst.data.fn_lit.body.offset + inst_idx];
                    const jump = lowerInst(lower, id, .implicit, .emit);
                    debug.assert(jump == .none, "emit mode should not jump");
                }
                const block = lower.insts[marker..lower.inst_count];
                lower.inst_count = marker;

                const typed_inst = lower.emit(.{
                    .pos = inst.pos,
                    .type = lower.results[@backingInt(inst_id)].known.type,
                    .tag = .func,
                    .data = .{ .block = lower.typed_ir.allocList(block) },
                });
                break :blk .{ .runtime = typed_inst };
            },
            .exec => blk: {
                const type_res = lower.results[@backingInt(inst.data.fn_lit.type)];
                const func_id = lower.ctx.func_table.add(.{
                    .file = lower.file_id,
                    .type = type_res.known.val.type,
                    .untyped_inst = inst_id,
                    .status = .unchecked,
                });
                break :blk .{ .known = .{
                    .type = type_res.known.val.type,
                    .val = .{ .fn_lit = func_id },
                } };
            },
        },

        .brk => switch (mode) {
            .emit => @panic("TODO"),
            .exec => return .{ .brk = .{
                .value = lower.results[@backingInt(inst.data.bin_op.rhs)].known,
                .block = inst.data.bin_op.lhs,
            } },
        },

        .brk_implicit => switch (mode) {
            .emit => @panic("TODO"),
            .exec => return .{ .brk = .{
                .value = .{ .type = lower.ctx.type_pool.literal(.void), .val = .void },
                .block = inst.data.unary_op,
            } },
        },

        .store => switch (mode) {
            .emit => blk: {
                const addr = lower.ref(inst.data.bin_op.lhs);
                const rhs = lower.ref(inst.data.bin_op.rhs);

                // TODO: coerce lhs to rhs pointer

                const typed_inst = lower.emit(.{
                    .type = lower.ctx.type_pool.literal(.void),
                    .pos = inst.pos,
                    .tag = .store,
                    .data = .{ .bin_op = .{ .lhs = addr, .rhs = rhs } },
                });
                break :blk .{ .runtime = typed_inst };
            },
            .exec => @panic("TODO"),
        },

        .load => switch (mode) {
            .emit => blk: {
                const addr = lower.ref(inst.data.unary_op);
                const addr_inst = lower.typed_ir.getInst(addr);
                const typed_inst = lower.emit(.{
                    .type = lower.ctx.type_pool.getType(addr_inst.type).data.ptr,
                    .pos = inst.pos,
                    .tag = .load,
                    .data = .{ .unary_op = addr },
                });
                break :blk .{ .runtime = typed_inst };
            },
            .exec => @panic("TODO"),
        },

        .alloc => switch (mode) {
            .emit => blk: {
                const type_id = lower.results[@backingInt(inst.data.unary_op)].known.val.type;
                const typed_inst = lower.emit(.{
                    .type = lower.ctx.type_pool.ptr(type_id),
                    .pos = inst.pos,
                    .tag = .alloc,
                    .data = .{ .alloc = type_id },
                });
                break :blk .{ .runtime = typed_inst };
            },
            .exec => @panic("TODO"),
        },

        .add, .subtract, .mul, .div, .mod => switch (mode) {
            .emit => blk: {
                const lhs = lower.results[@backingInt(inst.data.bin_op.lhs)];
                const rhs = lower.results[@backingInt(inst.data.bin_op.rhs)];
                if (lhs == .known and rhs == .known) {
                    @panic("TODO");
                } else {
                    const lhs_ref = lower.ref(inst.data.bin_op.lhs);
                    const rhs_ref = lower.ref(inst.data.bin_op.rhs);

                    const lhs_type = lower.typed_ir.getInst(lhs_ref).type;
                    const rhs_type = lower.typed_ir.getInst(rhs_ref).type;
                    const type_id = peerType(lower.ctx, lhs_type, rhs_type);
                    if (type_id == .none) {
                        @panic("TODO: handle type check error");
                    }

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
                    break :blk .{ .runtime = typed_inst };
                }
            },
            .exec => @panic("TODO"),
        },

        .global_ptr, .global_val => @panic("TODO: global name resolve"),

        .ret, .ret_implicit => switch (mode) {
            .emit => blk: {
                // TODO: remove ret_implicit based on coverage

                const val = lower.ref(inst.data.unary_op);
                const typed_inst = lower.emit(.{
                    .pos = inst.pos,
                    .tag = .ret,
                    .type = lower.ctx.type_pool.literal(.noreturn),
                    .data = .{ .unary_op = val },
                });
                break :blk .{ .runtime = typed_inst };
            },
            .exec => @panic("TODO"),
        },

        .type_lit => .{ .known = .{
            .type = lower.ctx.type_pool.literal(.type_id),
            .val = .{ .type = lower.ctx.type_pool.literal(inst.data.type_lit) },
        } },

        .undef_lit => .{ .known = .{
            .type = lower.ctx.type_pool.literal(.comp_undef),
            .val = .undef,
        } },

        .num_lit => blk: {
            const num_token = lexer.lexToken(file.contents, inst.pos);
            debug.assert(num_token.tag == .num_literal, "num lit lexed token invalid");
            const num_str = file.contents[num_token.start..num_token.end];
            const num = math.parseInt(i64, num_str) catch @panic("TODO: handle invalid num");
            break :blk .{ .known = .{
                .type = lower.ctx.type_pool.literal(.comp_int),
                .val = .{ .number = num },
            } };
        },

        .bool_lit => .{ .known = .{
            .type = lower.ctx.type_pool.literal(.bool),
            .val = .{ .boolean = inst.data.bool_lit },
        } },

        .type_of => .{ .known = .{
            .type = lower.ctx.type_pool.literal(.type_id),
            .val = .{ .type = lower.typeOf(inst.data.unary_op) },
        } },

        .fn_type => blk: {
            const ret = lower.results[@backingInt(inst.data.fn_type.return_type)].known.val.type;
            const args = lower.arena.pushArray(Type.Id, inst.data.fn_type.arg_types.count);
            for (0..inst.data.fn_type.arg_types.count) |i| {
                const arg = file.untyped_ir.extras[inst.data.fn_type.arg_types.offset + i];
                args[i] = lower.results[@backingInt(arg)].known.val.type;
            }
            break :blk .{ .known = .{
                .type = lower.ctx.type_pool.literal(.type_id),
                .val = .{ .type = lower.ctx.type_pool.func(ret, args) },
            } };
        },

        else => @panic("TODO"),
    };
    return .none;
}

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
