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
    var arena = mem.Arena{ .memory = bytes };

    const ctx = arena.pushStruct(Context);
    ctx.* = .{};

    _ = try loadFile(ctx, &arena, test_file);

    printer.debugPrintMessages(ctx);
}

const io = std.Io.Threaded.global_single_threaded.io();

fn loadFile(ctx: *Context, arena: *mem.Arena, path: []const u8) !File.Id {
    const file_handle = try std.Io.Dir.cwd().openFile(io, path, .{});
    defer file_handle.close(io);

    const len = try file_handle.length(io);
    const file_buf = arena.pushArray(u8, len);
    debug.assert(
        len == try file_handle.readPositionalAll(io, file_buf, 0),
        "file read incorrect size",
    );

    const ast = arena.pushStruct(Ast);
    ast.* = .{};

    const untyped_ir = arena.pushStruct(UntypedIr);
    untyped_ir.* = .{};

    const file_id = ctx.addFile(.{
        .path = path,
        .contents = file_buf,
        .ast = ast,
        .untyped_ir = untyped_ir,
    });

    const root_node = parser.parseFile(ctx, arena, file_id);
    printer.debugPrintAst(file_buf, ast, root_node, 0, true);

    const decls = untyped_lower.lowerFile(ctx, arena, file_id, root_node);
    for (decls) |decl| {
        debug.print("Decl: {s}\n", .{ctx.intern_pool.getString(decl.name)});
        if (decl.type != .none) {
            printer.debugPrintIr(file_buf, untyped_ir, decl.type, 0);
        }
        printer.debugPrintIr(file_buf, untyped_ir, decl.value, 0);
        debug.print("\n", .{});
    }

    return file_id;
}
