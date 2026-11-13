const stdx = @import("stdx.zig");
const debug = stdx.debug;

const Ast = @import("types.zig").Ast;
const Context = @import("types.zig").Context;
const File = @import("types.zig").File;
const UntypedIr = @import("types.zig").UntypedIr;
const TypedIr = @import("types.zig").TypedIr;
const Type = @import("types.zig").Type;
const Constant = @import("types.zig").Constant;
const InternPool = @import("types.zig").InternPool;

const lexer = @import("lexer.zig");

pub fn debugPrintMessages(ctx: *Context) void {
    debug.print("Messages:\n", .{});
    if (ctx.msg_count == 0) return;
    for (ctx.msgs[0..ctx.msg_count], 0..) |msg, id| {
        debug.print("{} {}\n", .{ id + 1, msg });
    }
}

pub fn debugPrintType(pool: *Type.Pool, id: Type.Id) void {
    if (id == .none) {
        debug.print("none", .{});
        return;
    }
    const t = pool.getType(id);
    switch (t) {
        .lit => debug.print("{s}", .{@tagName(id)}),
        .ptr => {
            debug.print("*", .{});
            debugPrintType(pool, t.ptr);
        },
        .func => {
            debug.print("fn (", .{});
            for (0..t.func.args.count) |i| {
                const arg_id = pool.extras[t.func.args.offset + i];
                debugPrintType(pool, arg_id);
            }
            debug.print(") ", .{});
            debugPrintType(pool, t.func.ret);
        },
    }
}

pub fn debugPrintConstant(pool: *Constant.Pool, id: Constant.Id) void {
    const c = pool.get(id);
    switch (c) {
        .undef => debug.print("#undefined", .{}),
        .bool => |v| debug.print("#{}", .{v}),
        .int => |v| debug.print("#{}", .{v}),
        .float => |v| debug.print("#{}", .{v}),
        .global => |v| debug.print("#global:{}", .{@backingInt(v)}),
    }
}

pub fn debugPrintTypedIr(
    ctx: *Context,
    ir: *TypedIr,
    inst_id: TypedIr.InstId,
    indent: u32,
) void {
    const inst = ir.getInst(inst_id);

    for (0..indent) |_| {
        debug.print("{s}", .{ir_indent});
    }
    debug.print("%{}: ", .{@backingInt(inst_id)});
    debugPrintType(&ctx.type_pool, inst.type);
    debug.print(" = ", .{});

    switch (inst.tag) {
        .constant => debugPrintConstant(&ctx.constant_pool, inst.data.constant),
        .add, .subtract, .mul, .div, .mod, .store => {
            debug.print("{s} %{} %{}", .{
                @tagName(inst.tag),
                @backingInt(inst.data.bin_op.lhs),
                @backingInt(inst.data.bin_op.rhs),
            });
        },

        .alloc => {
            debug.print("{s} ", .{@tagName(inst.tag)});
            debugPrintType(&ctx.type_pool, inst.data.alloc);
        },

        .load, .ret => {
            debug.print("{s} %{}", .{ @tagName(inst.tag), @backingInt(inst.data.unary_op) });
        },

        .func => {
            debug.print("{{\n", .{});
            for (0..inst.data.block.count) |child_inst_i| {
                const child_inst = ir.extras[inst.data.block.offset + child_inst_i];
                debugPrintTypedIr(ctx, ir, child_inst, indent + 1);
            }
            for (0..indent) |_| {
                debug.print("{s}", .{ir_indent});
            }
            debug.print("}}", .{});
        },
    }

    debug.print("\n", .{});
}

const ir_indent = "    ";
pub fn debugPrintIr(
    file: []const u8,
    ir: *UntypedIr,
    inst_id: UntypedIr.InstId,
    indent: u32,
) void {
    const inst = ir.getInst(inst_id);

    for (0..indent) |_| {
        debug.print("{s}", .{ir_indent});
    }

    switch (inst.tag) {
        .block, .comp_block => {
            debug.print("%{} = {s} {{\n", .{ @backingInt(inst_id), @tagName(inst.tag) });
            for (0..inst.data.block.count) |child_inst_i| {
                const child_inst = ir.extras[inst.data.block.offset + child_inst_i];
                debugPrintIr(file, ir, child_inst, indent + 1);
            }
            for (0..indent) |_| {
                debug.print("{s}", .{ir_indent});
            }
            debug.print("}}\n", .{});
        },
        .fn_type => {
            debug.print("%{} = fn_type ( ", .{
                @backingInt(inst_id),
            });
            for (0..inst.data.fn_type.arg_types.count) |arg_i| {
                const arg = ir.extras[inst.data.fn_type.arg_types.offset + arg_i];
                debug.print("%{} ", .{@backingInt(arg)});
            }
            debug.print(") %{}\n", .{@backingInt(inst.data.fn_type.return_type)});
        },
        .fn_lit => {
            debug.print("%{} = fn_lit %{} {{\n", .{
                @backingInt(inst_id),
                @backingInt(inst.data.fn_lit.type),
            });
            for (0..inst.data.fn_lit.body.count) |child_inst_i| {
                const child_inst = ir.extras[inst.data.fn_lit.body.offset + child_inst_i];
                debugPrintIr(file, ir, child_inst, indent + 1);
            }
            for (0..indent) |_| {
                debug.print("{s}", .{ir_indent});
            }
            debug.print("}}\n", .{});
        },

        .fn_arg => {
            const token = lexer.lexToken(file, inst.pos);
            const str = file[token.start..token.end];
            debug.print("%{} = {s} #{} \"{s}\"\n", .{
                @backingInt(inst_id),
                @tagName(inst.tag),
                inst.data.fn_arg.index,
                str,
            });
        },

        .num_lit, .type_lit, .bool_lit, .undef_lit, .reserved, .global_val, .global_ptr => {
            const token = lexer.lexToken(file, inst.pos);
            const str = file[token.start..token.end];
            debug.print("%{} = {s} #{s}\n", .{ @backingInt(inst_id), @tagName(inst.tag), str });
        },

        .add, .subtract, .mul, .div, .mod, .store, .brk, .coerce_type => {
            debug.print("%{} = {s} %{} %{}\n", .{
                @backingInt(inst_id),
                @tagName(inst.tag),
                @backingInt(inst.data.bin_op.lhs),
                @backingInt(inst.data.bin_op.rhs),
            });
        },
        .type_of, .load, .alloc, .negate, .ret, .brk_implicit, .ret_implicit => {
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
        .file, .block, .params => {
            const block = node.data.block;
            for (0..block.count) |idx| {
                const id = ast.extras[block.offset + idx];
                debugPrintAst(file, ast, id, child_len, idx == block.count - 1);
            }
        },

        .fn_type => {
            debugPrintAst(file, ast, node.data.fn_type.args, child_len, false);
            debugPrintAst(file, ast, node.data.fn_type.return_type, child_len, true);
        },
        .fn_lit => {
            debugPrintAst(file, ast, node.data.fn_lit.fn_type, child_len, false);
            debugPrintAst(file, ast, node.data.fn_lit.block, child_len, true);
        },

        .param => if (node.data.param.type != .none) {
            debugPrintAst(file, ast, node.data.param.type, child_len, true);
        },
        .const_decl, .var_decl => {
            debugPrintAst(file, ast, node.data.decl.param, child_len, false);
            debugPrintAst(file, ast, node.data.decl.value, child_len, true);
        },
        .negate, .ret => {
            debugPrintAst(file, ast, node.data.unary_op, child_len, true);
        },
        .add, .subtract, .mul, .div, .mod, .assign => {
            debugPrintAst(file, ast, node.data.bin_op.lhs, child_len, false);
            debugPrintAst(file, ast, node.data.bin_op.rhs, child_len, true);
        },

        .identifier, .type_lit, .bool_lit, .undef_lit, .num_lit => {},
    }
}
