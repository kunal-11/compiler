const stdx = @import("stdx.zig");
const mem = stdx.mem;
const debug = stdx.debug;

const std = @import("std");

const test_module = "testdir/mod1";
const test_file = test_module ++ "/main.pnx";

const Context = @import("types.zig").Context;
const Ast = @import("types.zig").Ast;
const UntypedIr = @import("types.zig").UntypedIr;
const TypedIr = @import("types.zig").TypedIr;
const File = @import("types.zig").File;
const Namespace = @import("types.zig").Namespace;
const Symbol = @import("types.zig").Symbol;

const parser = @import("parser.zig");
const untyped_lower = @import("lower_untyped.zig");
const printer = @import("printer.zig");
const analyzer = @import("analyzer.zig");

const roots = [_][]const u8{"main"};

pub fn main() !void {
    const bytes = try std.heap.page_allocator.alloc(u8, 64 * mem.MB);
    defer std.heap.page_allocator.free(bytes);
    var arena = mem.Arena{ .memory = bytes };

    const ctx = arena.pushStruct(Context);
    ctx.* = .{};

    const global_ns_id = ctx.addNamespace(&arena);
    _ = try loadFile(ctx, &arena, global_ns_id, test_file);

    analyzer.analyze(ctx, &arena);
    printer.debugPrintMessages(ctx);
}

const io = std.Io.Threaded.global_single_threaded.io();

fn loadFile(ctx: *Context, arena: *mem.Arena, ns_id: Namespace.Id, path: []const u8) !File.Id {
    var file_arena = arena.subArena(4 * mem.MB);

    const flusher = mem.Flusher.init(arena);
    defer flusher.flush();

    const file_handle = try std.Io.Dir.cwd().openFile(io, path, .{});
    defer file_handle.close(io);

    const len = try file_handle.length(io);
    const file_buf = file_arena.pushArray(u8, len);
    debug.assert(
        len == try file_handle.readPositionalAll(io, file_buf, 0),
        "file read incorrect size",
    );

    const ast = file_arena.pushStruct(Ast);
    ast.* = .{};

    const untyped_ir = file_arena.pushStruct(UntypedIr);
    untyped_ir.* = .{};

    const typed_ir = file_arena.pushStruct(TypedIr);
    typed_ir.* = .{};

    const ns = ctx.getNamespace(ns_id);
    const file_id = ctx.addFile(.{
        .arena = file_arena,
        .path = path,
        .contents = file_buf,
        .ast = ast,
        .untyped_ir = untyped_ir,
        .typed_ir = typed_ir,
    });

    const root_node = parser.parseFile(ctx, arena, file_id);
    printer.debugPrintAst(file_buf, ast, root_node, 0, true);

    const decls = untyped_lower.lowerFile(ctx, arena, file_id, root_node);
    for (decls) |decl| {
        debug.print("Decl: {s} {s}\n", .{
            ctx.intern_pool.getString(decl.name),
            @tagName(decl.tag),
        });
        if (decl.type != .none) {
            printer.debugPrintIr(file_buf, untyped_ir, decl.type, 0);
        }
        printer.debugPrintIr(file_buf, untyped_ir, decl.value, 0);
        debug.print("\n", .{});

        const symbol_id = ctx.symbol_table.add(.{
            .file = file_id,
            .tag = switch (decl.tag) {
                .const_decl => .constant,
                .var_decl => .variable,
            },
            .pos = decl.pos,
            .value_inst = decl.value,
            .type_inst = decl.type,
            .result = undefined,
        });

        switch (ns.add(decl.name, symbol_id)) {
            .duplicate => @panic("TODO: handle duplicate global decl"),
            .success => {},
        }

        for (roots) |root| {
            if (ctx.intern_pool.getOrCreateId(root) == decl.name) {
                ctx.analysis_q.push(.{ .decl = symbol_id });
            }
        }
    }

    return file_id;
}
