const stdx = @import("stdx.zig");
const mem = stdx.mem;

const Context = @import("types.zig").Context;
const Ast = @import("types.zig").Ast;
const File = @import("types.zig").File;
const Namespace = @import("types.zig").Namespace;
const Ir = @import("types.zig").UntypedIr;

const State = struct {
    arena: mem.Arena,

    ctx: *Context,
    file_id: File.Id,

    ast: *Ast,
    ir: *Ir,
    namespace: *Namespace,

    collector: Collector = .{},
};

const max_block_len = 4096;
const Collector = struct {
    insts: [max_block_len]Ir.InstId = undefined,
    inst_count: u32 = 0,

    pub fn pushNode(collector: *Collector, inst_id: Ir.InstId) void {
        collector.insts[collector.inst_count] = inst_id;
        collector.inst_count += 1;
    }
};

pub fn lowerDecl(ctx: *Context, ns_id: Namespace.Id, file_id: File.Id, node_id: Ast.NodeId) void {
    const flusher = mem.Flusher.init(&ctx.arena);
    defer flusher.flush();

    const file = ctx.getFile(file_id);
    const ns = ctx.getNamespace(ns_id);

    var state = State{
        .arena = ctx.arena.subArena(1 * mem.MB),
        .ctx = ctx,
        .file_id = file_id,

        .ast = file.ast,
        .ir = file.untyped_ir,
        .namespace = ns,
    };
    const decl_node = file.ast.getNode(node_id).data.decl;
    const param_node = file.ast.getNode(decl_node.param).data.param;

    const symbol_id = ns.find(param_node.intern_id);
    const symbol = ctx.symbol_table.get(symbol_id);
    if (param_node.type != .none) {
        symbol.type_inst = lowerBlock(&state, &.{param_node.type});
    }
    symbol.value_inst = lowerBlock(&state, &.{decl_node.value});
}

fn lowerBlock(state: *State, nodes: []const Ast.NodeId) Ir.InstId {
    const collect_marker = state.collector.inst_count;
    defer state.collector.inst_count = collect_marker;

    for (nodes) |node| {
        _ = lower(state, node);
    }

    const insts = state.collector.insts[collect_marker..state.collector.inst_count];
    return state.ir.allocInst(.{
        .pos = 0,
        .tag = .block,
        .data = .{ .block = insts },
    });
}

const max_fn_args = 1024;
fn lower(state: *State, node_id: Ast.NodeId) Ir.InstId {
    const node = state.ast.getNode(node_id);
    const id = switch (node.tag) {
        .block => lowerBlock(state, node.data.block),

        .num_lit => state.ir.allocInst(.{
            .pos = node.pos,
            .tag = .num_lit,
            .data = .{ .empty = {} },
        }),

        .intrinsic => state.ir.allocInst(.{
            .pos = node.pos,
            .tag = .intrinsic,
            .data = .{ .intrinsic = node.data.intrinsic },
        }),

        .fn_lit => blk: {
            const type_inst = lower(state, node.data.fn_lit.fn_type);

            const collect_marker = state.collector.inst_count;
            defer state.collector.inst_count = collect_marker;

            const type_node = state.ast.getNode(node.data.fn_lit.fn_type).data.fn_type;
            const args = state.ast.getNode(type_node.args).data.block;

            for (args, 0..) |arg, i| {
                const arg_node = state.ast.getNode(arg);
                // TODO: add the args for name resolution
                const arg_inst = state.ir.allocInst(.{
                    .pos = arg_node.pos,
                    .tag = .fn_arg,
                    .data = .{ .fn_arg = .{ .index = @intCast(i) } },
                });
                state.collector.pushNode(arg_inst);
            }

            const body_nodes = state.ast.getNode(node.data.fn_lit.block).data.block;
            for (body_nodes) |body_node| {
                _ = lower(state, body_node);
            }

            const body_insts = state.collector.insts[collect_marker..state.collector.inst_count];
            break :blk state.ir.allocInst(.{
                .pos = node.pos,
                .tag = .fn_lit,
                .data = .{ .fn_lit = .{
                    .type = type_inst,
                    .body = body_insts,
                } },
            });
        },
        .fn_type => blk: {
            const return_type = lower(state, node.data.fn_type.return_type);
            const params_node = state.ast.getNode(node.data.fn_type.args);

            const flusher = mem.Flusher.init(&state.arena);
            defer flusher.flush();

            const arg_buf = state.arena.pushArray(Ir.InstId, max_fn_args);
            var arg_count: u32 = 0;
            for (params_node.data.block) |arg| {
                // TODO: add the args for name resolution
                const arg_node = state.ast.getNode(arg).data.param;
                arg_buf[arg_count] = lower(state, arg_node.type);
                arg_count += 1;
            }

            break :blk state.ir.allocInst(.{
                .pos = node.pos,
                .tag = .fn_type,
                .data = .{ .fn_type = .{
                    .return_type = return_type,
                    .arg_types = arg_buf[0..arg_count],
                } },
            });
        },

        .const_decl => blk: {
            const param = state.ast.getNode(node.data.decl.param).data.param;

            const type_inst = if (param.type != .none) lower(state, param.type) else .none;
            const value_inst = lower(state, node.data.decl.value);

            const inst = state.ir.allocInst(.{
                .pos = node.pos,
                .tag = .alloc_const,
                .data = .{ .decl = .{
                    .type = type_inst,
                    .value = value_inst,
                } },
            });

            // TODO: add the param decl to name resolution
            break :blk inst;
        },
        .var_decl => blk: {
            const param = state.ast.getNode(node.data.decl.param).data.param;

            const type_inst = if (param.type != .none) lower(state, param.type) else .none;
            const value_inst = lower(state, node.data.decl.value);

            const inst = state.ir.allocInst(.{
                .pos = node.pos,
                .tag = .alloc_var,
                .data = .{ .decl = .{
                    .type = type_inst,
                    .value = value_inst,
                } },
            });

            // TODO: add the param decl to name resolution
            break :blk inst;
        },
        .identifier => blk: {
            // TODO: resolve the name of the identifier
            const inst = state.ir.allocInst(.{
                .pos = node.pos,
                .tag = .identifier,
                .data = .{ .empty = {} },
            });
            break :blk inst;
        },

        .add => state.ir.allocInst(.{
            .pos = node.pos,
            .tag = .add,
            .data = .{ .bin_op = .{
                .lhs = lower(state, node.data.bin_op.lhs),
                .rhs = lower(state, node.data.bin_op.rhs),
            } },
        }),
        .subtract => state.ir.allocInst(.{
            .pos = node.pos,
            .tag = .subtract,
            .data = .{ .bin_op = .{
                .lhs = lower(state, node.data.bin_op.lhs),
                .rhs = lower(state, node.data.bin_op.rhs),
            } },
        }),
        .mul => state.ir.allocInst(.{
            .pos = node.pos,
            .tag = .mul,
            .data = .{ .bin_op = .{
                .lhs = lower(state, node.data.bin_op.lhs),
                .rhs = lower(state, node.data.bin_op.rhs),
            } },
        }),
        .div => state.ir.allocInst(.{
            .pos = node.pos,
            .tag = .div,
            .data = .{ .bin_op = .{
                .lhs = lower(state, node.data.bin_op.lhs),
                .rhs = lower(state, node.data.bin_op.rhs),
            } },
        }),
        .mod => state.ir.allocInst(.{
            .pos = node.pos,
            .tag = .mod,
            .data = .{ .bin_op = .{
                .lhs = lower(state, node.data.bin_op.lhs),
                .rhs = lower(state, node.data.bin_op.rhs),
            } },
        }),
        .assign => state.ir.allocInst(.{
            .pos = node.pos,
            .tag = .assign,
            .data = .{ .bin_op = .{
                .lhs = lower(state, node.data.bin_op.lhs),
                .rhs = lower(state, node.data.bin_op.rhs),
            } },
        }),
        .negate => state.ir.allocInst(.{
            .pos = node.pos,
            .tag = .negate,
            .data = .{ .unary_op = lower(state, node.data.unary_op) },
        }),
        else => @panic("unknown node lowered"),
    };
    state.collector.pushNode(id);
    return id;
}
