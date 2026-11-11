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
            .runtime => |child_id| lower.typed_ir.getInst(child_id).type,
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
    const res = lowerInst(state, inst_id, res_type, .exec);
    debug.assert(res.control == .none, "global block must break to itself");
    return state;
}

const Mode = enum { emit, exec };

pub fn lowerInst(
    state: *State,
    inst_id: UntypedIr.InstId,
    res_type: ResultType,
    mode: Mode,
) Result {
    const inst = state.untyped_ir.getInst(inst_id);
    const res: Result = switch (inst.tag) {
        .comp_block => lowerCompBlock(state, inst_id, res_type, mode),
        .fn_lit => lowerFnLit(state, inst_id, mode),

        .alloc => lowerAlloc(state, inst_id, mode),
        .load => lowerLoad(state, inst_id, mode),
        .store => lowerStore(state, inst_id, mode),

        .fn_type => lowerFnType(state, inst_id),
        .num_lit => lowerNumLit(state, inst_id),

        .type_lit => .{ .value = .{ .known = .{
            .type = state.ctx.type_pool.literal(.type_id),
            .val = .{ .type = state.ctx.type_pool.literal(inst.data.type_lit) },
        } } },

        .undef_lit => .{ .value = .{ .known = .{
            .type = state.ctx.type_pool.literal(.comp_undef),
            .val = .undef,
        } } },

        .bool_lit => .{ .value = .{ .known = .{
            .type = state.ctx.type_pool.literal(.bool),
            .val = .{ .boolean = inst.data.bool_lit },
        } } },

        .type_of => .{ .value = .{ .known = .{
            .type = state.ctx.type_pool.literal(.type_id),
            .val = .{ .type = state.typeOf(inst.data.unary_op) },
        } } },

        .brk => switch (mode) {
            .emit => @panic("TODO"),
            .exec => return .{
                .value = state.results[@backingInt(inst.data.bin_op.rhs)],
                .control = .{ .brk = inst.data.bin_op.lhs },
            },
        },
        .brk_implicit => switch (mode) {
            .emit => @panic("TODO"),
            .exec => return .{
                .value = .{ .known = .{
                    .type = state.ctx.type_pool.literal(.void),
                    .val = .void,
                } },
                .control = .{ .brk = inst.data.unary_op },
            },
        },

        .add, .subtract, .mul, .div, .mod => lowerInfixOp(state, inst_id, res_type, mode),

        .global_ptr, .global_val => @panic("TODO: global name resolve"),

        .ret, .ret_implicit => switch (mode) {
            .emit => blk: {
                // TODO: remove ret_implicit based on coverage

                const val = state.ref(inst.data.unary_op);
                const typed_inst = state.emit(.{
                    .pos = inst.pos,
                    .tag = .ret,
                    .type = state.ctx.type_pool.literal(.noreturn),
                    .data = .{ .unary_op = val },
                });
                break :blk .{ .value = .{ .runtime = typed_inst } };
            },
            .exec => @panic("TODO"),
        },

        else => @panic("TODO"),
    };
    state.results[@backingInt(inst_id)] = res.value;
    return res;
}

const Result = struct {
    value: Value,
    control: union(enum) {
        none,
        ret,
        brk: UntypedIr.InstId,
    } = .none,
};

fn lowerStore(state: *State, inst_id: UntypedIr.InstId, mode: Mode) Result {
    const inst = state.untyped_ir.getInst(inst_id);
    return switch (mode) {
        .emit => {
            const addr = state.ref(inst.data.bin_op.lhs);
            const rhs = state.ref(inst.data.bin_op.rhs);

            // TODO: coerce lhs to rhs pointer
            const typed_inst = state.emit(.{
                .type = state.ctx.type_pool.literal(.void),
                .pos = inst.pos,
                .tag = .store,
                .data = .{ .bin_op = .{ .lhs = addr, .rhs = rhs } },
            });
            return .{ .value = .{ .runtime = typed_inst } };
        },
        .exec => @panic("TODO"),
    };
}

fn lowerLoad(state: *State, inst_id: UntypedIr.InstId, mode: Mode) Result {
    const inst = state.untyped_ir.getInst(inst_id);
    switch (mode) {
        .emit => {
            const addr = state.ref(inst.data.unary_op);
            const addr_inst = state.typed_ir.getInst(addr);
            const typed_inst = state.emit(.{
                .type = state.ctx.type_pool.getType(addr_inst.type).data.ptr,
                .pos = inst.pos,
                .tag = .load,
                .data = .{ .unary_op = addr },
            });
            return .{ .value = .{ .runtime = typed_inst } };
        },
        .exec => @panic("TODO"),
    }
}

fn lowerAlloc(state: *State, inst_id: UntypedIr.InstId, mode: Mode) Result {
    const inst = state.untyped_ir.getInst(inst_id);
    return switch (mode) {
        .emit => {
            const type_id = state.results[@backingInt(inst.data.unary_op)].known.val.type;
            const typed_inst = state.emit(.{
                .type = state.ctx.type_pool.ptr(type_id),
                .pos = inst.pos,
                .tag = .alloc,
                .data = .{ .alloc = type_id },
            });
            return .{ .value = .{ .runtime = typed_inst } };
        },
        .exec => @panic("TODO"),
    };
}

fn lowerCompBlock(
    state: *State,
    inst_id: UntypedIr.InstId,
    res_type: ResultType,
    mode: Mode,
) Result {
    const inst = state.untyped_ir.getInst(inst_id);
    return switch (mode) {
        .emit => {
            const res = lowerInst(state, inst_id, res_type, .exec);
            debug.assert(res.control == .none, "comp block cannot break in emit");
            return .{ .value = state.results[@backingInt(inst_id)] };
        },
        .exec => {
            for (0..inst.data.block.count) |inst_idx| {
                const child_id = state.untyped_ir.extras[inst.data.block.offset + inst_idx];
                const res = lowerInst(state, child_id, res_type, .exec);
                switch (res.control) {
                    .none => {},
                    .ret => @panic("TODO"),
                    .brk => |block| if (block == inst_id)
                        return .{ .value = res.value }
                    else
                        return res,
                }
            }
            @panic("block did not end with break");
        },
    };
}

fn lowerInfixOp(state: *State, inst_id: UntypedIr.InstId, res_type: ResultType, mode: Mode) Result {
    _ = res_type;
    const inst = state.untyped_ir.getInst(inst_id);
    return switch (mode) {
        .emit => {
            const lhs = state.results[@backingInt(inst.data.bin_op.lhs)];
            const rhs = state.results[@backingInt(inst.data.bin_op.rhs)];
            if (lhs == .known and rhs == .known) {
                @panic("TODO");
            } else {
                const lhs_ref = state.ref(inst.data.bin_op.lhs);
                const rhs_ref = state.ref(inst.data.bin_op.rhs);

                const lhs_type = state.typed_ir.getInst(lhs_ref).type;
                const rhs_type = state.typed_ir.getInst(rhs_ref).type;
                const type_id = peerType(state.ctx, lhs_type, rhs_type);
                if (type_id == .none) {
                    @panic("TODO: handle type check error");
                }

                const typed_inst = state.emit(.{
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
                return .{ .value = .{ .runtime = typed_inst } };
            }
        },
        .exec => @panic("TODO"),
    };
}

fn lowerFnLit(state: *State, inst_id: UntypedIr.InstId, mode: Mode) Result {
    const inst = state.untyped_ir.getInst(inst_id);
    switch (mode) {
        .emit => {
            const marker = state.inst_count;
            for (0..inst.data.fn_lit.body.count) |inst_idx| {
                const id = state.untyped_ir.extras[inst.data.fn_lit.body.offset + inst_idx];
                const jump = lowerInst(state, id, .implicit, .emit);
                debug.assert(jump.control == .none, "emit mode should not jump");
            }
            const block = state.insts[marker..state.inst_count];
            state.inst_count = marker;

            const typed_inst = state.emit(.{
                .pos = inst.pos,
                .type = state.results[@backingInt(inst_id)].known.type,
                .tag = .func,
                .data = .{ .block = state.typed_ir.allocList(block) },
            });
            return .{ .value = .{ .runtime = typed_inst } };
        },
        .exec => {
            const type_res = state.results[@backingInt(inst.data.fn_lit.type)];
            const func_id = state.ctx.func_table.add(.{
                .file = state.file_id,
                .type = type_res.known.val.type,
                .untyped_inst = inst_id,
                .status = .unchecked,
            });
            return .{ .value = .{ .known = .{
                .type = type_res.known.val.type,
                .val = .{ .fn_lit = func_id },
            } } };
        },
    }
}

fn lowerNumLit(state: *State, inst_id: UntypedIr.InstId) Result {
    const file = state.ctx.getFile(state.file_id);
    const inst = state.untyped_ir.getInst(inst_id);
    const num_token = lexer.lexToken(file.contents, inst.pos);
    debug.assert(num_token.tag == .num_literal, "num lit lexed token invalid");
    const num_str = file.contents[num_token.start..num_token.end];
    const num = math.parseInt(i64, num_str) catch @panic("TODO: handle invalid num");
    return .{ .value = .{ .known = .{
        .type = state.ctx.type_pool.literal(.comp_int),
        .val = .{ .number = num },
    } } };
}

fn lowerFnType(state: *State, inst_id: UntypedIr.InstId) Result {
    const inst = state.untyped_ir.getInst(inst_id);
    const ret = state.results[@backingInt(inst.data.fn_type.return_type)].known.val.type;
    const args = state.arena.pushArray(Type.Id, inst.data.fn_type.arg_types.count);
    for (0..inst.data.fn_type.arg_types.count) |i| {
        const arg = state.untyped_ir.extras[inst.data.fn_type.arg_types.offset + i];
        args[i] = state.results[@backingInt(arg)].known.val.type;
    }
    return .{ .value = .{ .known = .{
        .type = state.ctx.type_pool.literal(.type_id),
        .val = .{ .type = state.ctx.type_pool.func(ret, args) },
    } } };
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
