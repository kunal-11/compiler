const stdx = @import("stdx.zig");
const mem = stdx.mem;
const debug = stdx.debug;

const Context = @import("types.zig").Context;
const Ast = @import("types.zig").Ast;
const File = @import("types.zig").File;
const Ir = @import("types.zig").UntypedIr;
const InternPool = @import("types.zig").InternPool;

const State = struct {
    const max_instructions = 4096;
    const max_blocks = 128;

    const Block = struct {
        marker: u32,
        reserved_id: Ir.InstId,
        tag: enum { any, function, compile },
    };

    const Phase = union(enum) {
        function: Ir.InstId, // the type inst
        compile: u32, // nesting count
    };

    arena: mem.Arena,
    ast: *Ast,
    ir: *Ir,

    insts: [max_instructions]Ir.InstId = undefined,
    inst_count: u32 = 0,

    blocks: [max_blocks]Block = undefined,
    block_count: u32 = 0,

    phases: [max_blocks]Phase = undefined,
    phase_count: u32 = 0,

    pub fn emit(state: *State, inst: Ir.Inst) Ir.InstId {
        const inst_id = state.ir.allocInst(inst);
        state.insts[state.inst_count] = inst_id;
        state.inst_count += 1;
        return inst_id;
    }

    pub fn beginBlock(state: *State) void {
        state.blocks[state.block_count] = .{
            .marker = state.inst_count,
            .tag = .any,
            .reserved_id = state.ir.allocInst(.{
                .tag = .reserved,
                .pos = 0,
                .data = .{ .empty = {} },
            }),
        };
        state.block_count += 1;
    }

    pub fn beginFnBlock(state: *State, type_inst: Ir.InstId) void {
        state.blocks[state.block_count] = .{
            .marker = state.inst_count,
            .tag = .function,
            .reserved_id = state.ir.allocInst(.{
                .tag = .reserved,
                .pos = 0,
                .data = .{ .empty = {} },
            }),
        };
        state.block_count += 1;
        state.phases[state.phase_count] = .{ .function = type_inst };
        state.phase_count += 1;
    }

    pub fn beginCompileBlock(state: *State) void {
        var block_id = Ir.InstId.none;
        if (state.phase_count > 0 and state.phases[state.phase_count - 1] == .compile) {
            state.phases[state.phase_count - 1].compile += 1;
        } else {
            state.phases[state.phase_count] = .{ .compile = 1 };
            state.phase_count += 1;
            block_id = state.ir.allocInst(.{
                .tag = .reserved,
                .pos = 0,
                .data = .{ .empty = {} },
            });
        }

        state.blocks[state.block_count] = .{
            .marker = state.inst_count,
            .tag = .compile,
            .reserved_id = block_id,
        };
        state.block_count += 1;
    }

    pub fn emitBlock(state: *State, pos: u32, result: Ir.InstId) Ir.InstId {
        const block = state.blocks[state.block_count - 1];
        state.block_count -= 1;

        var phase = &state.phases[state.phase_count - 1];
        if (block.tag == .compile and phase.compile > 1) {
            phase.compile -= 1;
            return result;
        }

        if (block.tag == .compile or block.tag == .function) {
            state.phase_count -= 1;
        }

        debug.assert(block.reserved_id != .none, "block reserved id invalid");
        switch (block.tag) {
            .compile, .any => {
                if (result != .none) {
                    _ = state.emit(.{
                        .pos = pos,
                        .tag = .brk,
                        .data = .{ .bin_op = .{
                            .lhs = block.reserved_id,
                            .rhs = result,
                        } },
                    });
                } else {
                    _ = state.emit(.{
                        .pos = pos,
                        .tag = .brk_implicit,
                        .data = .{ .unary_op = block.reserved_id },
                    });
                }
            },
            .function => {
                debug.assert(result == .none, "function block cannot have implicit result");
                _ = state.emit(.{
                    .pos = pos,
                    .tag = .ret_implicit,
                    .data = .{ .unary_op = block.reserved_id },
                });
            },
        }

        const insts = state.insts[block.marker..state.inst_count];
        state.inst_count = block.marker;

        const inst: Ir.Inst = switch (block.tag) {
            .any => .{
                .pos = pos,
                .tag = .block,
                .data = .{ .block = insts },
            },
            .compile => .{
                .pos = pos,
                .tag = .comp_block,
                .data = .{ .block = insts },
            },
            .function => .{
                .pos = pos,
                .tag = .fn_lit,
                .data = .{ .fn_lit = .{ .type = phase.function, .body = insts } },
            },
        };

        state.ir.overwriteInst(block.reserved_id, inst);
        state.insts[state.inst_count] = block.reserved_id;
        state.inst_count += 1;
        return block.reserved_id;
    }
};

pub const Decl = struct {
    pos: u32,
    name: InternPool.Id,
    type: Ir.InstId,
    value: Ir.InstId,
};

const max_decls = 1024;
pub fn lowerFile(ctx: *Context, arena: *mem.Arena, file_id: File.Id, root_id: Ast.NodeId) []Decl {
    const result = arena.pushArray(Decl, max_decls);
    var result_count: u32 = 0;

    const flusher = mem.Flusher.init(arena);
    defer flusher.flush();

    const file = ctx.getFile(file_id);
    var state = State{
        .arena = arena.subArena(1 * mem.MB),
        .ast = file.ast,
        .ir = file.untyped_ir,
    };

    const node = state.ast.getNode(root_id);
    debug.assert(node.tag == .file, "ast root for lower is not a file");

    for (node.data.block) |global| {
        const decl_node = state.ast.getNode(global);
        const param_node = state.ast.getNode(decl_node.data.decl.param);

        const type_inst = if (param_node.data.param.type != .none) blk: {
            state.beginCompileBlock();
            const res = lower(&state, param_node.data.param.type);
            break :blk state.emitBlock(param_node.pos, res);
        } else .none;

        const value_node = state.ast.getNode(decl_node.data.decl.value);
        state.beginCompileBlock();
        const res = lower(&state, decl_node.data.decl.value);
        const value_inst = state.emitBlock(value_node.pos, res);

        result[result_count] = .{
            .pos = param_node.pos,
            .name = param_node.data.param.intern_id,
            .type = type_inst,
            .value = value_inst,
        };
        result_count += 1;
    }

    return result[0..result_count];
}

const max_fn_args = 1024;
fn lower(state: *State, node_id: Ast.NodeId) Ir.InstId {
    const node = state.ast.getNode(node_id);
    return switch (node.tag) {
        .block => blk: {
            state.beginBlock();
            for (node.data.block) |child| {
                _ = lower(state, child);
            }
            break :blk state.emitBlock(node.pos, .none);
        },

        .num_lit => state.emit(.{
            .pos = node.pos,
            .tag = .num_lit,
            .data = .{ .empty = {} },
        }),
        .undef_lit => state.emit(.{
            .pos = node.pos,
            .tag = .undef_lit,
            .data = .{ .empty = {} },
        }),
        .bool_lit => state.emit(.{
            .pos = node.pos,
            .tag = .bool_lit,
            .data = .{ .bool_lit = node.data.bool_lit },
        }),
        .type_lit => state.emit(.{
            .pos = node.pos,
            .tag = .type_lit,
            .data = .{ .type_lit = node.data.type_lit },
        }),

        .fn_lit => blk: {
            const type_node = state.ast.getNode(node.data.fn_lit.fn_type);
            const type_inst = blk1: {
                state.beginCompileBlock();
                const res = lower(state, node.data.fn_lit.fn_type);
                break :blk1 state.emitBlock(type_node.pos, res);
            };

            state.beginFnBlock(type_inst);
            const args = state.ast.getNode(type_node.data.fn_type.args).data.block;
            for (args, 0..) |arg, i| {
                const arg_node = state.ast.getNode(arg);
                // TODO: add the args for name resolution
                _ = state.emit(.{
                    .pos = arg_node.pos,
                    .tag = .fn_arg,
                    .data = .{ .fn_arg = .{ .index = @intCast(i) } },
                });
            }
            const body_nodes = state.ast.getNode(node.data.fn_lit.block).data.block;
            for (body_nodes) |body_node| {
                _ = lower(state, body_node);
            }
            break :blk state.emitBlock(node.pos, .none);
        },
        .fn_type => blk: {
            const flusher = mem.Flusher.init(&state.arena);
            defer flusher.flush();

            state.beginCompileBlock();

            const arg_buf = state.arena.pushArray(Ir.InstId, max_fn_args);
            var arg_count: u32 = 0;
            const params_node = state.ast.getNode(node.data.fn_type.args);
            for (params_node.data.block) |arg| {
                const arg_node = state.ast.getNode(arg);
                arg_buf[arg_count] = lower(state, arg_node.data.param.type);
                arg_count += 1;

                // TODO: add the args for name resolution
            }

            const return_type = lower(state, node.data.fn_type.return_type);
            const res = state.emit(.{
                .pos = node.pos,
                .tag = .fn_type,
                .data = .{ .fn_type = .{
                    .return_type = return_type,
                    .arg_types = arg_buf[0..arg_count],
                } },
            });
            break :blk state.emitBlock(node.pos, res);
        },

        .const_decl => blk: {
            // TODO: add the param decl to name resolution
            const param = state.ast.getNode(node.data.decl.param);
            if (param.data.param.type != .none) {
                @panic("TODO: explicitly typed local constants");
            }

            state.beginCompileBlock();
            const value_node = state.ast.getNode(node.data.decl.value);
            const res = lower(state, node.data.decl.value);
            break :blk state.emitBlock(value_node.pos, res);
        },
        .var_decl => blk: {
            const value_inst = lower(state, node.data.decl.value);

            const param = state.ast.getNode(node.data.decl.param);
            const type_inst = if (param.data.param.type != .none) blk1: {
                state.beginCompileBlock();
                const res = lower(state, param.data.param.type);
                break :blk1 state.emitBlock(node.pos, res);
            } else state.emit(.{
                .pos = node.pos,
                .tag = .type_of,
                .data = .{ .unary_op = value_inst },
            });

            const inst = state.emit(.{
                .pos = param.pos,
                .tag = .alloc,
                .data = .{ .bin_op = .{ .lhs = type_inst, .rhs = value_inst } },
            });

            // TODO: add the param decl to name resolution
            break :blk inst;
        },
        .identifier => blk: {
            // TODO: resolve the name of the identifier
            const inst = state.emit(.{
                .pos = node.pos,
                .tag = .identifier,
                .data = .{ .empty = {} },
            });
            break :blk inst;
        },

        .add, .subtract, .mul, .div, .mod, .assign => blk: {
            const lhs = lower(state, node.data.bin_op.lhs);
            const rhs = lower(state, node.data.bin_op.rhs);
            break :blk state.emit(.{
                .pos = node.pos,
                .tag = switch (node.tag) {
                    .add => .add,
                    .subtract => .subtract,
                    .mul => .mul,
                    .div => .div,
                    .mod => .mod,
                    .assign => .assign,
                    else => @panic("lower bin op table incomplete"),
                },
                .data = .{ .bin_op = .{
                    .lhs = lhs,
                    .rhs = rhs,
                } },
            });
        },
        .negate => state.emit(.{
            .pos = node.pos,
            .tag = .negate,
            .data = .{ .unary_op = lower(state, node.data.unary_op) },
        }),

        .file, .param, .params => @panic("lower invalid node"),
    };
}
