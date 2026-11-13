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
        inst_marker: u32,
        undo_marker: u32,
        reserved_id: Ir.InstId,
        tag: enum { any, function, compile },
    };

    const Phase = union(enum) {
        function: Ir.InstId, // the type inst
        compile: u32, // nesting count
    };

    arena: mem.Arena,
    ctx: *Context,
    ast: *Ast,
    ir: *Ir,

    file_id: File.Id,

    insts: [max_instructions]Ir.InstId = undefined,
    inst_count: u32 = 0,

    blocks: [max_blocks]Block = undefined,
    block_count: u32 = 0,

    phases: [max_blocks]Phase = undefined,
    phase_count: u32 = 0,

    name_table: NameTable = .{},

    pub fn emit(state: *State, inst: Ir.Inst) Ir.InstId {
        const inst_id = state.ir.allocInst(inst);
        state.insts[state.inst_count] = inst_id;
        state.inst_count += 1;
        return inst_id;
    }

    pub fn beginBlock(state: *State) void {
        state.blocks[state.block_count] = .{
            .inst_marker = state.inst_count,
            .undo_marker = state.name_table.undo_len,
            .tag = .any,
            .reserved_id = state.ir.allocInst(.{
                .tag = .reserved,
                .pos = 0,
                .data = .{ .empty = {} },
            }),
        };
        state.block_count += 1;

        state.name_table.lexical_depth += 1;
    }

    pub fn beginFnBlock(state: *State, type_inst: Ir.InstId) void {
        state.blocks[state.block_count] = .{
            .undo_marker = state.name_table.undo_len,
            .inst_marker = state.inst_count,
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

        state.name_table.fn_depth += 1;
        state.name_table.lexical_depth += 1;
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

        state.name_table.lexical_depth += 1;

        state.blocks[state.block_count] = .{
            .undo_marker = state.name_table.undo_len,
            .inst_marker = state.inst_count,
            .tag = .compile,
            .reserved_id = block_id,
        };
        state.block_count += 1;
    }

    pub fn emitBlock(state: *State, pos: u32, result: Ir.InstId) Ir.InstId {
        const block = state.blocks[state.block_count - 1];
        state.block_count -= 1;

        state.name_table.undo(block.undo_marker);
        if (block.tag == .function) {
            state.name_table.fn_depth -= 1;
        }
        state.name_table.lexical_depth -= 1;

        const phase = state.phases[state.phase_count - 1];
        if (block.tag == .compile and phase.compile > 1) {
            state.phases[state.phase_count - 1].compile -= 1;
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
                    .data = .{ .unary_op = .none },
                });
            },
        }

        const insts = state.insts[block.inst_marker..state.inst_count];
        state.inst_count = block.inst_marker;

        const inst: Ir.Inst = switch (block.tag) {
            .any => .{
                .pos = pos,
                .tag = .block,
                .data = .{ .block = state.ir.allocList(insts) },
            },
            .compile => .{
                .pos = pos,
                .tag = .comp_block,
                .data = .{ .block = state.ir.allocList(insts) },
            },
            .function => .{
                .pos = pos,
                .tag = .fn_lit,
                .data = .{ .fn_lit = .{
                    .type = phase.function,
                    .body = state.ir.allocList(insts),
                } },
            },
        };

        state.ir.overwriteInst(block.reserved_id, inst);
        state.insts[state.inst_count] = block.reserved_id;
        state.inst_count += 1;
        return block.reserved_id;
    }
};

const Name = struct {
    pos: u32,
    intern_id: InternPool.Id,
    inst: Ir.InstId,
    tag: enum { arg, constant, variable },
};

const NameTable = struct {
    const max_names = 8192;

    const Item = struct {
        name: Name,
        fn_depth: u16,
        lexical_depth: u16,
    };

    names: [max_names]Item = @splat(.{
        .name = .{
            .intern_id = .none,
            .inst = .none,
            .pos = undefined,
            .tag = undefined,
        },
        .fn_depth = undefined,
        .lexical_depth = undefined,
    }),

    // hack: inst is set to none for deletion entries
    undo_stack: [max_names]Item = undefined,
    undo_len: u32 = 0,

    fn_depth: u16 = 0,
    lexical_depth: u16 = 0,

    const max_probes = max_names / 4;
    fn getSlot(table: *NameTable, id: InternPool.Id) *Item {
        debug.assert(id != .none, "name table slot for none");

        const hash = @backingInt(id) % max_names;
        var probe: u32 = 0;
        while (probe < max_probes) : (probe += 1) {
            const slot = table.names[(hash + probe) % max_names];
            if (slot.name.intern_id == .none or slot.name.intern_id == id) break;
        }

        debug.assert(probe < max_probes, "name table OOM");
        return &table.names[(hash + probe) % max_names];
    }

    pub const AddResult = union(enum) {
        success,
        redeclared: Name,
    };

    pub fn addName(table: *NameTable, name: Name) AddResult {
        const slot = table.getSlot(name.intern_id);

        // shadowing rule
        if (slot.name.intern_id != .none) {
            return .{ .redeclared = slot.name };
        }

        table.undo_stack[table.undo_len] = .{
            .name = .{
                .intern_id = name.intern_id,
                .pos = slot.name.pos,
                .inst = slot.name.inst,
                .tag = slot.name.tag,
            },
            .fn_depth = slot.fn_depth,
            .lexical_depth = slot.lexical_depth,
        };
        table.undo_len += 1;

        slot.* = .{
            .name = name,
            .fn_depth = table.fn_depth,
            .lexical_depth = table.lexical_depth,
        };
        return .success;
    }

    pub const FindResult = union(enum) {
        empty,
        closure: Name,
        success: Name,
    };

    pub fn findName(table: *NameTable, id: InternPool.Id) FindResult {
        debug.assert(id != .none, "");
        const slot = table.getSlot(id);

        if (slot.name.intern_id == .none) return .empty;

        debug.assert(slot.name.intern_id == id, "");

        // check for closures, 0 is global scope which is allowed for global vars
        // other enclosing function mutables or args not allowed
        if (slot.fn_depth > 0 and slot.fn_depth < table.fn_depth) {
            if (slot.name.tag == .variable or slot.name.tag == .arg)
                return .{ .closure = slot.name };
        }

        return .{ .success = slot.name };
    }

    pub fn undo(table: *NameTable, marker: u32) void {
        while (table.undo_len > marker) : (table.undo_len -= 1) {
            var item = table.undo_stack[table.undo_len - 1];
            const slot = table.getSlot(item.name.intern_id);
            if (item.name.inst == .none) {
                item.name.intern_id = .none;
            }
            slot.* = item;
        }
    }
};

pub const Decl = struct {
    pos: u32,
    name: InternPool.Id,
    tag: enum { var_decl, const_decl },
    value: Ir.InstId,
};

const max_decls = 1024;
pub fn lowerFile(ctx: *Context, arena: *mem.Arena, file_id: File.Id, root_id: Ast.NodeId) []Decl {
    const result = arena.pushArray(Decl, max_decls);
    var result_count: u32 = 0;

    const flusher = mem.Flusher.init(arena);
    defer flusher.flush();

    const file = ctx.getFile(file_id);
    const state = arena.pushStruct(State);
    state.* = .{
        .arena = arena.subArena(1 * mem.MB),
        .ctx = ctx,
        .ast = file.ast,
        .ir = file.untyped_ir,
        .file_id = file_id,
    };

    const node = state.ast.getNode(root_id);
    debug.assert(node.tag == .file, "ast root for lower is not a file");

    for (0..node.data.block.count) |global_i| {
        const global = state.ast.extras[node.data.block.offset + global_i];
        const decl_node = state.ast.getNode(global);
        const param_node = state.ast.getNode(decl_node.data.decl.param);

        state.beginCompileBlock();
        const type_inst = if (param_node.data.param.type != .none)
            lower(state, param_node.data.param.type, .none)
        else
            .none;
        const value_node = state.ast.getNode(decl_node.data.decl.value);
        const res = lower(state, decl_node.data.decl.value, type_inst);
        const value_inst = state.emitBlock(value_node.pos, res);

        result[result_count] = .{
            .pos = param_node.pos,
            .name = param_node.data.param.intern_id,
            .value = value_inst,
            .tag = switch (decl_node.tag) {
                .var_decl => .var_decl,
                .const_decl => .const_decl,
                else => @panic("unkown global node lowered"),
            },
        };
        result_count += 1;
    }

    return result[0..result_count];
}

fn lowerPtr(state: *State, node_id: Ast.NodeId) Ir.InstId {
    debug.assert(node_id != .none, "lower none node");
    if (node_id == .poison) return .poison;

    const node = state.ast.getNode(node_id);
    return switch (node.tag) {
        .identifier => blk: {
            const id = node.data.identifier.intern_id;
            switch (state.name_table.findName(id)) {
                .closure => |name| {
                    state.ctx.addMsg(.{
                        .severity = .err,
                        .pos = .{ .file = state.file_id, .offset = node.pos },
                        .data = .{ .closure_on_variable = .{
                            .original_pos = .{
                                .file = state.file_id,
                                .offset = name.pos,
                            },
                        } },
                    });
                    break :blk .poison;
                },
                .empty => {
                    break :blk state.emit(.{
                        .pos = node.pos,
                        .tag = .global_ptr,
                        .data = .{ .global_ref = id },
                    });
                },
                .success => |name| {
                    const inst = switch (name.tag) {
                        .constant, .arg => blk1: {
                            state.ctx.addMsg(.{
                                .severity = .err,
                                .pos = .{ .file = state.file_id, .offset = node.pos },
                                .data = .expected_lvalue,
                            });
                            break :blk1 .poison;
                        },
                        .variable => name.inst,
                    };
                    break :blk inst;
                },
            }
        },
        else => blk1: {
            state.ctx.addMsg(.{
                .severity = .err,
                .pos = .{ .file = state.file_id, .offset = node.pos },
                .data = .expected_lvalue,
            });
            break :blk1 .poison;
        },
    };
}

const max_fn_args = 1024;
fn lower(state: *State, node_id: Ast.NodeId, res_type: Ir.InstId) Ir.InstId {
    debug.assert(node_id != .none, "lower none node");
    if (node_id == .poison) return .poison;

    const node = state.ast.getNode(node_id);
    const value = switch (node.tag) {
        .block => blk: {
            state.beginBlock();
            for (0..node.data.block.count) |child_idx| {
                const child = state.ast.extras[node.data.block.offset + child_idx];
                _ = lower(state, child, .none);
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
            state.beginCompileBlock();
            const type_inst = lower(state, node.data.fn_lit.fn_type, .none);
            const lit = blk1: {
                state.beginFnBlock(type_inst);
                const type_node = state.ast.getNode(node.data.fn_lit.fn_type);
                const args = state.ast.getNode(type_node.data.fn_type.args).data.block;
                for (0..args.count) |i| {
                    const arg = state.ast.extras[args.offset + i];
                    const arg_node = state.ast.getNode(arg);
                    const inst = state.emit(.{
                        .pos = arg_node.pos,
                        .tag = .fn_arg,
                        .data = .{ .fn_arg = .{ .index = @intCast(i) } },
                    });

                    const name = Name{
                        .pos = arg_node.pos,
                        .intern_id = arg_node.data.param.intern_id,
                        .inst = inst,
                        .tag = .arg,
                    };
                    switch (state.name_table.addName(name)) {
                        .redeclared => |og_name| {
                            state.ctx.addMsg(.{
                                .pos = .{
                                    .file = state.file_id,
                                    .offset = arg_node.pos,
                                },
                                .severity = .err,
                                .data = .{ .duplicate_decl = .{
                                    .original_pos = .{
                                        .file = state.file_id,
                                        .offset = og_name.pos,
                                    },
                                } },
                            });
                        },
                        .success => {},
                    }
                }
                const body_nodes = state.ast.getNode(node.data.fn_lit.block).data.block;
                for (0..body_nodes.count) |body_node_idx| {
                    const body_node = state.ast.extras[body_nodes.offset + body_node_idx];
                    _ = lower(state, body_node, .none);
                }
                break :blk1 state.emitBlock(node.pos, .none);
            };
            break :blk state.emitBlock(node.pos, lit);
        },
        .fn_type => blk: {
            state.beginCompileBlock();

            const flusher = mem.Flusher.init(&state.arena);
            defer flusher.flush();

            const params_node = state.ast.getNode(node.data.fn_type.args);
            const arg_buf = state.arena.pushArray(Ir.InstId, max_fn_args);
            var arg_count: u32 = 0;
            for (0..params_node.data.block.count) |arg_i| {
                const arg = state.ast.extras[params_node.data.block.offset + arg_i];
                const arg_node = state.ast.getNode(arg);
                arg_buf[arg_count] = lower(state, arg_node.data.param.type, .none);
                arg_count += 1;
            }

            const return_type = lower(state, node.data.fn_type.return_type, .none);
            const res = state.emit(.{
                .pos = node.pos,
                .tag = .fn_type,
                .data = .{ .fn_type = .{
                    .return_type = return_type,
                    .arg_types = state.ir.allocList(arg_buf[0..arg_count]),
                } },
            });
            break :blk state.emitBlock(node.pos, res);
        },

        .const_decl => blk: {
            state.beginCompileBlock();

            const param = state.ast.getNode(node.data.decl.param);
            const type_inst = if (param.data.param.type != .none)
                lower(state, param.data.param.type, .none)
            else
                .none;

            const res = lower(state, node.data.decl.value, type_inst);
            const inst = state.emitBlock(node.pos, res);

            const name = Name{
                .pos = param.pos,
                .intern_id = param.data.param.intern_id,
                .inst = inst,
                .tag = .constant,
            };
            switch (state.name_table.addName(name)) {
                .redeclared => |og_name| {
                    state.ctx.addMsg(.{
                        .pos = .{
                            .file = state.file_id,
                            .offset = param.pos,
                        },
                        .severity = .err,
                        .data = .{ .duplicate_decl = .{
                            .original_pos = .{
                                .file = state.file_id,
                                .offset = og_name.pos,
                            },
                        } },
                    });
                },
                .success => {},
            }
            break :blk inst;
        },
        .var_decl => blk: {
            const param = state.ast.getNode(node.data.decl.param);
            const type_inst = if (param.data.param.type != .none) blk1: {
                state.beginCompileBlock();
                const res = lower(state, param.data.param.type, .none);
                break :blk1 state.emitBlock(node.pos, res);
            } else .none;

            const value_inst = lower(state, node.data.decl.value, type_inst);
            const value_type = state.emit(.{
                .pos = param.pos,
                .tag = .type_of,
                .data = .{ .unary_op = value_inst },
            });
            const inst = state.emit(.{
                .pos = param.pos,
                .tag = .alloc,
                .data = .{ .unary_op = value_type },
            });
            _ = state.emit(.{
                .pos = node.pos,
                .tag = .store,
                .data = .{ .bin_op = .{
                    .lhs = inst,
                    .rhs = value_inst,
                } },
            });
            const name = Name{
                .pos = param.pos,
                .intern_id = param.data.param.intern_id,
                .inst = inst,
                .tag = .variable,
            };
            switch (state.name_table.addName(name)) {
                .redeclared => |og_name| {
                    state.ctx.addMsg(.{
                        .pos = .{
                            .file = state.file_id,
                            .offset = param.pos,
                        },
                        .severity = .err,
                        .data = .{ .duplicate_decl = .{
                            .original_pos = .{
                                .file = state.file_id,
                                .offset = og_name.pos,
                            },
                        } },
                    });
                },
                .success => {},
            }
            break :blk inst;
        },
        .identifier => blk: {
            const id = node.data.identifier.intern_id;
            switch (state.name_table.findName(id)) {
                .empty => {
                    break :blk state.emit(.{
                        .pos = node.pos,
                        .tag = .global_val,
                        .data = .{ .global_ref = id },
                    });
                },
                .closure => |name| {
                    state.ctx.addMsg(.{
                        .severity = .err,
                        .pos = .{ .file = state.file_id, .offset = node.pos },
                        .data = .{ .closure_on_variable = .{
                            .original_pos = .{
                                .file = state.file_id,
                                .offset = name.pos,
                            },
                        } },
                    });
                    break :blk .poison;
                },
                .success => |name| {
                    const inst = switch (name.tag) {
                        .constant, .arg => name.inst,
                        .variable => state.emit(.{
                            .pos = node.pos,
                            .tag = .load,
                            .data = .{ .unary_op = name.inst },
                        }),
                    };
                    break :blk inst;
                },
            }
        },

        .assign => blk: {
            debug.assert(res_type == .none, "");
            const lvalue = lowerPtr(state, node.data.bin_op.lhs);
            const rvalue = lower(state, node.data.bin_op.rhs, .none);
            break :blk state.emit(.{
                .pos = node.pos,
                .tag = .store,
                .data = .{ .bin_op = .{
                    .lhs = lvalue,
                    .rhs = rvalue,
                } },
            });
        },

        .add, .subtract, .mul, .div, .mod => blk: {
            const lhs = lower(state, node.data.bin_op.lhs, .none);
            const rhs = lower(state, node.data.bin_op.rhs, .none);
            break :blk state.emit(.{
                .pos = node.pos,
                .tag = switch (node.tag) {
                    .add => .add,
                    .subtract => .subtract,
                    .mul => .mul,
                    .div => .div,
                    .mod => .mod,
                    else => @panic("lower binary op table incomplete"),
                },
                .data = .{ .bin_op = .{
                    .lhs = lhs,
                    .rhs = rhs,
                } },
            });
        },

        .ret => blk: {
            const value = if (node.data.unary_op == .none)
                .none
            else
                lower(state, node.data.unary_op, .none);

            break :blk state.emit(.{
                .pos = node.pos,
                .tag = .ret,
                .data = .{ .unary_op = value },
            });
        },
        .negate => blk: {
            const value = lower(state, node.data.unary_op, .none);
            break :blk state.emit(.{
                .pos = node.pos,
                .tag = switch (node.tag) {
                    .negate => .negate,
                    else => @panic("lower unary op table incomplete"),
                },
                .data = .{ .unary_op = value },
            });
        },

        .file, .param, .params => @panic("lower invalid node"),
    };

    if (res_type != .none) {
        const cast = state.emit(.{
            .pos = node.pos,
            .tag = .coerce_type,
            .data = .{ .bin_op = .{ .lhs = res_type, .rhs = value } },
        });
        return cast;
    }

    return value;
}
