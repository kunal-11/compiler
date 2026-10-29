const stdx = @import("stdx.zig");
const mem = stdx.mem;
const debug = stdx.debug;

const std = @import("std");

const test_module = "testdir/mod1";
const test_file = "testdir/mod1/main.pnx";

const Context = @import("types.zig").Context;
const Ast = @import("types.zig").Ast;
const UntypedIr = @import("types.zig").UntypedIr;
const File = @import("types.zig").File;
const Namespace = @import("types.zig").Namespace;

const parser = @import("parser.zig");
const untyped_lower = @import("lower_untyped.zig");
const printer = @import("printer.zig");

pub fn main() !void {
    const bytes = try std.heap.page_allocator.alloc(u8, 64 * mem.MB);
    defer std.heap.page_allocator.free(bytes);

    const ctx: *Context = @ptrCast(@alignCast(bytes[0..@sizeOf(Context)]));
    ctx.* = .{
        .arena = .{ .memory = bytes, .used = @sizeOf(Context) },
    };

    const ns_id = ctx.addNamespace();
    _ = try loadFile(ctx, test_file, ns_id);

    printer.debugPrintMessages(ctx);
}

const io = std.Io.Threaded.global_single_threaded.io();

fn loadFile(ctx: *Context, path: []const u8, ns_id: Namespace.Id) !File.Id {
    const file_handle = try std.Io.Dir.cwd().openFile(io, path, .{});
    defer file_handle.close(io);

    const len = try file_handle.length(io);
    const file_buf = ctx.arena.pushArray(u8, len);
    debug.assert(
        len == try file_handle.readPositionalAll(io, file_buf, 0),
        "file read incorrect size",
    );

    const ast = ctx.arena.pushStruct(Ast);
    ast.* = .{};

    const untyped_ir = ctx.arena.pushStruct(UntypedIr);
    untyped_ir.* = .{};

    const file_id = ctx.addFile(.{
        .path = path,
        .contents = file_buf,
        .ast = ast,
        .untyped_ir = untyped_ir,
    });

    const decls = parser.parseFile(ctx, file_id);
    const ns = ctx.getNamespace(ns_id);
    for (decls) |decl| {
        const symbol_id = ctx.symbol_table.add(.{ .file = file_id, .ast_node = decl });

        const decl_node = ast.getNode(decl);
        const param_node = ast.getNode(decl_node.data.decl.param);

        debug.print("\n", .{});

        const ns_ok = ns.add(param_node.data.param.intern_id, symbol_id);
        if (ns_ok != symbol_id) {
            const og_decl = ctx.symbol_table.get(ns_ok);
            const og_node = ctx.getFile(og_decl.file).ast.getNode(og_decl.ast_node);
            ctx.addMsg(.{
                .severity = .err,
                .pos = .{ .file = file_id, .offset = param_node.pos },
                .data = .{ .duplicate_decl = .{
                    .original_pos = .{ .file = og_decl.file, .offset = og_node.pos },
                } },
            });
        } else printer.debugPrintAst(file_buf, ast, decl, 0, true);

        untyped_lower.lowerDecl(ctx, ns_id, file_id, decl);

        debug.print("\n", .{});

        const symbol = ctx.symbol_table.get(symbol_id);
        if (symbol.type_inst != .none) {
            printer.debugPrintIr(file_buf, untyped_ir, symbol.type_inst, 0);
        }
        printer.debugPrintIr(file_buf, untyped_ir, symbol.value_inst, 0);

        debug.print("\n \n", .{});
    }

    return file_id;
}
