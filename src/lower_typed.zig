const stdx = @import("stdx.zig");
const mem = stdx.mem;
const debug = stdx.debug;
const math = stdx.math;

const Context = @import("types.zig").Context;
const File = @import("types.zig").File;
const Type = @import("types.zig").Type;
const Func = @import("types.zig").Func;
const Namespace = @import("types.zig").Namespace;
const Constant = @import("types.zig").Constant;
const InternPool = @import("types.zig").InternPool;
const Symbol = @import("types.zig").Symbol;

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
    poison,
    known: Known,
    runtime: TypedIr.InstId,

    fn expectType(value: Value) !Type.Id {
        return switch (value) {
            .none, .poison => @panic("none, poison type"),
            .runtime => error.RuntimeInst,
            .known => |known| switch (known.val) {
                .type => |t| t,
                else => error.InvalidType,
            },
        };
    }
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

    const Name = union(enum) {
        none,
        symbol: Symbol.Id,
        type: Type.Id,
    };

    fn resolveName(state: *State, intern_id: InternPool.Id) Name {
        const symbol = state.namespace.find(intern_id);
        if (symbol != .none) return .{ .symbol = symbol };

        const name_str = state.ctx.intern_pool.getString(intern_id);
        const t = state.ctx.type_pool.parseLiteral(name_str);
        if (t != .none) return .{ .type = t };

        return .none;
    }

    fn emit(lower: *State, inst: TypedIr.Inst) TypedIr.InstId {
        const inst_id = lower.typed_ir.allocInst(inst);
        lower.insts[lower.inst_count] = inst_id;
        lower.inst_count += 1;
        return inst_id;
    }

    fn typeOf(lower: *State, value: Value) Type.Id {
        return switch (value) {
            .none => @panic("type of none value"),
            .poison => @panic("type of poison"),
            .known => |val| val.type,
            .runtime => |child_id| lower.typed_ir.getInst(child_id).type,
        };
    }

    fn getOperand(state: *State, inst_id: UntypedIr.InstId) ?Value {
        debug.assert(inst_id != .none, "get none operand");
        if (inst_id == .poison) return null;
        const val = state.results[@backingInt(inst_id)];
        return switch (val) {
            .none => @panic("get none operand"),
            .poison => null,
            .known, .runtime => val,
        };
    }

    fn ref(lower: *State, val: Value) TypedIr.InstId {
        return switch (val) {
            .known => |value| blk: {
                const const_id: Constant.Id = switch (value.val) {
                    .undef => .undef,
                    .number => lower.ctx.constant_pool.int(value.val.number),
                    .boolean => if (value.val.boolean) .bool_true else .bool_false,
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
            .poison => @panic("ref of poison"),
            .none => @panic("invalid ref for none inst"),
        };
    }

    fn coerce(state: *State, val: Value, t_id: Type.Id) !Value {
        switch (val) {
            .none, .poison => @panic("cast on none/poison"),
            .known => |known| {
                if (known.type == t_id) return val;

                const t = state.ctx.type_pool.getType(t_id);
                switch (known.type) {
                    .comp_int => {
                        if (t == .fixed_int) {
                            return .{ .known = .{ .type = t_id, .val = known.val } };
                        }
                    },
                    else => {},
                }
                return error.IncompatibleTypes;
            },
            .runtime => |inst_id| {
                const inst = state.typed_ir.getInst(inst_id);
                if (inst.type == t_id) return val;
                return error.IncompatibleTypes;
            },
        }
    }

    fn peerType(state: *State, t1_id: Type.Id, t2_id: Type.Id) !Type.Id {
        _ = state;
        if (t1_id == t2_id) return t1_id;
        if (t1_id == .comp_int) return t2_id;
        if (t2_id == .comp_int) return t1_id;

        return error.IncompatibleTypes;
    }
};

pub fn evalBlock(
    ctx: *Context,
    arena: *mem.Arena,
    file_id: File.Id,
    inst_id: UntypedIr.InstId,
) *State {
    const state = State.init(ctx, file_id, arena);
    const res = lowerInst(state, inst_id, .exec);
    debug.assert(res.control == .none, "global block must break to itself");
    return state;
}

const Mode = enum { emit, exec };

pub fn lowerInst(state: *State, inst_id: UntypedIr.InstId, mode: Mode) Result {
    const inst = state.untyped_ir.getInst(inst_id);
    const res: Result = switch (inst.tag) {
        .comp_block => lowerCompBlock(state, inst_id, mode),
        .fn_lit => lowerFnLit(state, inst_id, mode),

        .alloc => lowerAlloc(state, inst_id, mode),
        .load => lowerLoad(state, inst_id, mode),
        .store => lowerStore(state, inst_id, mode),

        .fn_type => lowerFnType(state, inst_id),
        .num_lit => lowerNumLit(state, inst_id),

        .undef_lit => .{ .value = .{ .known = .{
            .type = .comp_undef,
            .val = .undef,
        } } },

        .bool_lit => .{ .value = .{ .known = .{
            .type = .bool,
            .val = .{ .boolean = inst.data.bool_lit },
        } } },

        .type_of => blk: {
            const val = state.getOperand(inst.data.unary_op) orelse {
                break :blk .{ .value = .poison };
            };
            break :blk .{ .value = .{ .known = .{
                .type = .type_id,
                .val = .{ .type = state.typeOf(val) },
            } } };
        },

        .coerce_type => blk: {
            const type_value = state.getOperand(inst.data.bin_op.lhs) orelse {
                break :blk .{ .value = .poison };
            };
            const type_id = type_value.expectType() catch {
                state.ctx.addMsg(.{
                    .severity = .err,
                    .pos = .{ .file = state.file_id, .offset = inst.pos },
                    .data = .expected_type,
                });
                break :blk .{ .value = .poison };
            };
            const value = state.getOperand(inst.data.bin_op.rhs) orelse {
                break :blk .{ .value = .poison };
            };
            const cast_val = state.coerce(value, type_id) catch err: {
                state.ctx.addMsg(.{
                    .severity = .err,
                    .pos = .{ .file = state.file_id, .offset = inst.pos },
                    .data = .incompatible_cast,
                });
                break :err .poison;
            };
            break :blk .{ .value = cast_val };
        },

        .brk => switch (mode) {
            .emit => @panic("TODO"),
            .exec => return .{
                .value = state.getOperand(inst.data.bin_op.rhs) orelse .poison,
                .control = .{ .brk = inst.data.bin_op.lhs },
            },
        },
        .brk_implicit => switch (mode) {
            .emit => @panic("TODO"),
            .exec => return .{
                .value = .{ .known = .{
                    .type = .void,
                    .val = .void,
                } },
                .control = .{ .brk = inst.data.unary_op },
            },
        },

        .add, .subtract, .mul, .div, .mod => lowerInfixOp(state, inst_id, mode),

        .global_ptr => @panic("TODO: global ptr resolve"),

        .global_val => blk: {
            const name = state.resolveName(inst.data.global_ref);
            switch (name) {
                .none => {
                    state.ctx.addMsg(.{
                        .severity = .err,
                        .pos = .{ .file = state.file_id, .offset = inst.pos },
                        .data = .undeclared_identifier,
                    });
                    break :blk .{ .value = .poison };
                },
                .type => |t| break :blk .{ .value = .{ .known = .{
                    .type = .type_id,
                    .val = .{ .type = t },
                } } },
                .symbol => |symbol_id| {
                    // TODO: emit a load and error in exec in case of variable

                    // TODO: check if already evaled and reuse value
                    const symbol = state.ctx.symbol_table.get(symbol_id);
                    const child_state = evalBlock(
                        state.ctx,
                        state.arena,
                        symbol.file,
                        symbol.value_inst,
                    );
                    const child_value = child_state.getOperand(symbol.value_inst) orelse
                        break :blk .{ .value = .poison };
                    break :blk .{ .value = child_value };
                },
            }
        },

        .ret_implicit => switch (mode) {
            .emit => blk: {
                const typed_inst = state.emit(.{
                    .pos = inst.pos,
                    .tag = .ret,
                    .type = .noreturn,
                    .data = .{ .unary_op = .none },
                });
                break :blk .{ .value = .{ .runtime = typed_inst } };
            },
            .exec => @panic("TODO"),
        },
        .ret => switch (mode) {
            .emit => blk: {
                const val = if (inst.data.unary_op != .none) blk1: {
                    const value = state.getOperand(inst.data.unary_op) orelse {
                        break :blk .{ .value = .poison };
                    };
                    break :blk1 state.ref(value);
                } else .none;
                const typed_inst = state.emit(.{
                    .pos = inst.pos,
                    .tag = .ret,
                    .type = .noreturn,
                    .data = .{ .unary_op = val },
                });
                break :blk .{ .value = .{ .runtime = typed_inst } };
            },
            .exec => @panic("TODO"),
        },

        else => @panic("TODO"),
    };
    state.results[@backingInt(inst_id)] = res.value;

    // debug.log("%{} = {}", .{ @backingInt(inst_id), res.value });
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

    const addr = state.getOperand(inst.data.bin_op.lhs) orelse return .{ .value = .poison };
    const addr_type_id = state.typeOf(addr);
    const addr_type = state.ctx.type_pool.getType(addr_type_id);
    if (addr_type != .ptr) {
        state.ctx.addMsg(.{
            .severity = .err,
            .pos = .{ .file = state.file_id, .offset = inst.pos },
            .data = .exptected_ptr,
        });
        return .{ .value = .poison };
    }

    const rhs = state.getOperand(inst.data.bin_op.rhs) orelse return .{ .value = .poison };
    const value = state.coerce(rhs, addr_type.ptr) catch {
        state.ctx.addMsg(.{
            .severity = .err,
            .pos = .{ .file = state.file_id, .offset = inst.pos },
            .data = .incompatible_cast,
        });
        return .{ .value = .poison };
    };

    return switch (mode) {
        .emit => {
            const addr_ref = state.ref(addr);
            const val_ref = state.ref(value);
            const typed_inst = state.emit(.{
                .type = .void,
                .pos = inst.pos,
                .tag = .store,
                .data = .{ .bin_op = .{ .lhs = addr_ref, .rhs = val_ref } },
            });
            return .{ .value = .{ .runtime = typed_inst } };
        },
        .exec => @panic("TODO"),
    };
}

fn lowerLoad(state: *State, inst_id: UntypedIr.InstId, mode: Mode) Result {
    const inst = state.untyped_ir.getInst(inst_id);
    const op = state.getOperand(inst.data.unary_op) orelse return .{ .value = .poison };
    const op_type_id = state.typeOf(op);
    const op_type = state.ctx.type_pool.getType(op_type_id);
    debug.assert(op_type == .ptr, "load must be ptr");
    switch (mode) {
        .emit => {
            const addr_ref = state.ref(op);
            const typed_inst = state.emit(.{
                .type = op_type.ptr,
                .pos = inst.pos,
                .tag = .load,
                .data = .{ .unary_op = addr_ref },
            });
            return .{ .value = .{ .runtime = typed_inst } };
        },
        .exec => @panic("TODO"),
    }
}

fn lowerAlloc(state: *State, inst_id: UntypedIr.InstId, mode: Mode) Result {
    const inst = state.untyped_ir.getInst(inst_id);
    const type_val = state.getOperand(inst.data.unary_op) orelse return .{ .value = .poison };
    const type_id = type_val.expectType() catch {
        state.ctx.addMsg(.{
            .severity = .err,
            .pos = .{ .file = state.file_id, .offset = inst.pos },
            .data = .expected_type,
        });
        return .{ .value = .poison };
    };
    switch (type_id) {
        .comp_float, .comp_int, .comp_undef, .type_id, .void, .noreturn => {
            state.ctx.addMsg(.{
                .pos = .{ .file = state.file_id, .offset = inst.pos },
                .severity = .err,
                .data = .addr_of_comp_type,
            });
            return .{ .value = .poison };
        },
        else => {},
    }

    return switch (mode) {
        .emit => {
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

fn lowerCompBlock(state: *State, inst_id: UntypedIr.InstId, mode: Mode) Result {
    const inst = state.untyped_ir.getInst(inst_id);
    return switch (mode) {
        .emit => {
            const res = lowerInst(state, inst_id, .exec);
            debug.assert(res.control == .none, "comp block cannot break in emit");
            return .{ .value = state.results[@backingInt(inst_id)] };
        },
        .exec => {
            for (0..inst.data.block.count) |inst_idx| {
                const child_id = state.untyped_ir.extras[inst.data.block.offset + inst_idx];
                const res = lowerInst(state, child_id, .exec);
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

fn lowerInfixOp(state: *State, inst_id: UntypedIr.InstId, mode: Mode) Result {
    const inst = state.untyped_ir.getInst(inst_id);
    const lhs = state.getOperand(inst.data.bin_op.lhs) orelse return .{ .value = .poison };
    const rhs = state.getOperand(inst.data.bin_op.rhs) orelse return .{ .value = .poison };

    const lhs_type_id = state.typeOf(lhs);
    const rhs_type_id = state.typeOf(rhs);
    const peer_type_id = state.peerType(lhs_type_id, rhs_type_id) catch {
        state.ctx.addMsg(.{
            .severity = .err,
            .pos = .{ .file = state.file_id, .offset = inst.pos },
            .data = .incompatible_peer_types,
        });
        return .{ .value = .poison };
    };

    const lhs_cast = state.coerce(lhs, peer_type_id) catch {
        state.ctx.addMsg(.{
            .severity = .err,
            .pos = .{ .file = state.file_id, .offset = inst.pos },
            .data = .incompatible_cast,
        });
        return .{ .value = .poison };
    };
    const rhs_cast = state.coerce(rhs, peer_type_id) catch {
        state.ctx.addMsg(.{
            .severity = .err,
            .pos = .{ .file = state.file_id, .offset = inst.pos },
            .data = .incompatible_cast,
        });
        return .{ .value = .poison };
    };

    return switch (mode) {
        .emit => {
            if (lhs == .known and rhs == .known) {
                @panic("TODO");
            } else {
                const lhs_ref = state.ref(lhs_cast);
                const rhs_ref = state.ref(rhs_cast);

                const typed_inst = state.emit(.{
                    .pos = inst.pos,
                    .type = peer_type_id,
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
                const jump = lowerInst(state, id, .emit);
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
            const type_res = state.getOperand(inst.data.fn_lit.type) orelse {
                return .{ .value = .poison };
            };
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
        .type = .comp_int,
        .val = .{ .number = num },
    } } };
}

fn lowerFnType(state: *State, inst_id: UntypedIr.InstId) Result {
    const inst = state.untyped_ir.getInst(inst_id);
    const ret_value = state.getOperand(inst.data.fn_type.return_type) orelse {
        return .{ .value = .poison };
    };
    const ret = ret_value.expectType() catch {
        const ret_inst = state.untyped_ir.getInst(inst.data.fn_type.return_type);
        state.ctx.addMsg(.{
            .severity = .err,
            .pos = .{ .file = state.file_id, .offset = ret_inst.pos },
            .data = .expected_type,
        });
        return .{ .value = .poison };
    };

    const args = state.arena.pushArray(Type.Id, inst.data.fn_type.arg_types.count);
    for (0..inst.data.fn_type.arg_types.count) |i| {
        const arg = state.untyped_ir.extras[inst.data.fn_type.arg_types.offset + i];
        const arg_value = state.getOperand(arg) orelse return .{ .value = .poison };
        args[i] = arg_value.expectType() catch {
            const arg_inst = state.untyped_ir.getInst(arg);
            state.ctx.addMsg(.{
                .severity = .err,
                .pos = .{ .file = state.file_id, .offset = arg_inst.pos },
                .data = .expected_type,
            });
            return .{ .value = .poison };
        };
    }
    return .{ .value = .{ .known = .{
        .type = .type_id,
        .val = .{ .type = state.ctx.type_pool.func(ret, args) },
    } } };
}
