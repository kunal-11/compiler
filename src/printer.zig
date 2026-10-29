const stdx = @import("stdx.zig");
const debug = stdx.debug;

const Ast = @import("types.zig").Ast;
const Context = @import("types.zig").Context;
const File = @import("types.zig").File;
const UntypedIr = @import("types.zig").UntypedIr;

const lexer = @import("lexer.zig");

pub fn debugPrintMessages(ctx: *Context) void {
    if (ctx.msg_count == 0) return;
    for (ctx.msgs[0..ctx.msg_count], 0..) |msg, id| {
        debug.print("{} {}\n", .{ id + 1, msg });
    }
}

const ir_indent = "    ";
pub fn debugPrintIr(file: []const u8, ir: *UntypedIr, inst_id: UntypedIr.InstId, indent: u32) void {
    const inst = ir.getInst(inst_id);

    for (0..indent) |_| {
        debug.print("{s}", .{ir_indent});
    }

    switch (inst.tag) {
        .block => {
            debug.print("%{} = block {{\n", .{@backingInt(inst_id)});
            for (inst.data.block) |child_inst| {
                debugPrintIr(file, ir, child_inst, indent + 1);
            }
            debug.print("}}\n", .{});
        },
        .fn_type => {
            debug.print("%{} = fn_type ( ", .{
                @backingInt(inst_id),
            });
            for (inst.data.fn_type.arg_types) |arg| {
                debug.print("%{} ", .{@backingInt(arg)});
            }
            debug.print(") %{}\n", .{@backingInt(inst.data.fn_type.return_type)});
        },
        .fn_lit => {
            debug.print("%{} = fn_lit %{} {{\n", .{
                @backingInt(inst_id),
                @backingInt(inst.data.fn_lit.type),
            });
            for (inst.data.fn_lit.body) |child_inst| {
                debugPrintIr(file, ir, child_inst, indent + 1);
            }
            debug.print("{s}}}\n", .{ir_indent});
        },

        .fn_arg => {
            debug.print("%{} = {s} #{}\n", .{
                @backingInt(inst_id),
                @tagName(inst.tag),
                inst.data.fn_arg.index,
            });
        },

        .num_lit, .intrinsic, .identifier => {
            const token = lexer.lexToken(file, inst.pos);
            const str = file[token.start..token.end];
            debug.print("%{} = {s} #{s}\n", .{ @backingInt(inst_id), @tagName(inst.tag), str });
        },

        .alloc_const, .alloc_var => {
            debug.print("%{} = {s} %{} = %{}\n", .{
                @backingInt(inst_id),
                @tagName(inst.tag),
                @backingInt(inst.data.decl.type),
                @backingInt(inst.data.decl.value),
            });
        },

        .add, .subtract, .mul, .div, .mod, .assign => {
            debug.print("%{} = {s} %{} %{}\n", .{
                @backingInt(inst_id),
                @tagName(inst.tag),
                @backingInt(inst.data.bin_op.lhs),
                @backingInt(inst.data.bin_op.rhs),
            });
        },
        .negate => {
            debug.print("%{} = {s} %{}\n", .{
                @backingInt(inst_id),
                @tagName(inst.tag),
                @backingInt(inst.data.unary_op),
            });
        },
    }
}

const middle_self_fmt = "├── ";
const last_self_fmt = "└── ";

const middle_child_fmt = "│   ";
const last_child_fmt = "    ";

var print_buf: [4096]u8 = undefined;
pub fn debugPrintAst(
    file: []const u8,
    ast: *Ast,
    node_id: Ast.NodeId,
    prefix_len: usize,
    is_last: bool,
) void {
    const node = ast.getNode(node_id);
    const token = lexer.lexToken(file, node.pos);

    const prefix = print_buf[0..prefix_len];
    const self_fmt = if (is_last) last_self_fmt else middle_self_fmt;

    const child_fmt = if (is_last) last_child_fmt else middle_child_fmt;
    for (child_fmt, 0..) |char, i| {
        print_buf[prefix_len + i] = char;
    }
    const child_len = prefix_len + child_fmt.len;

    const token_str = file[token.start..token.end];
    debug.print("{s}{s}{s} {s}\n", .{ prefix, self_fmt, @tagName(node.tag), token_str });

    switch (node.tag) {
        .identifier, .intrinsic, .num_lit => {},

        .fn_type => {
            debugPrintAst(file, ast, node.data.fn_type.args, child_len, false);
            debugPrintAst(file, ast, node.data.fn_type.return_type, child_len, true);
        },
        .fn_lit => {
            debugPrintAst(file, ast, node.data.fn_lit.fn_type, child_len, false);
            debugPrintAst(file, ast, node.data.fn_lit.block, child_len, true);
        },
        .block, .params => {
            const block = node.data.block;
            for (block, 0..) |id, idx| {
                debugPrintAst(file, ast, id, child_len, idx == block.len - 1);
            }
        },
        .param => if (node.data.param.type != .none) {
            debugPrintAst(file, ast, node.data.param.type, child_len, true);
        },
        .const_decl, .var_decl => {
            debugPrintAst(file, ast, node.data.decl.param, child_len, false);
            debugPrintAst(file, ast, node.data.decl.value, child_len, true);
        },
        .negate => {
            debugPrintAst(file, ast, node.data.unary_op, child_len, true);
        },
        .add, .subtract, .mul, .div, .mod, .assign => {
            debugPrintAst(file, ast, node.data.bin_op.lhs, child_len, false);
            debugPrintAst(file, ast, node.data.bin_op.rhs, child_len, true);
        },
    }
}
