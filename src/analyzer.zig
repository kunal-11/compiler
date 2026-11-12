const stdx = @import("stdx.zig");
const mem = stdx.mem;
const debug = stdx.debug;
const math = stdx.math;

const Context = @import("types.zig").Context;
const Symbol = @import("types.zig").Symbol;
const Func = @import("types.zig").Func;

const typed_lower = @import("lower_typed.zig");
const lexer = @import("lexer.zig");

pub const Queue = struct {
    pub const Item = union(enum) {
        empty,
        decl: Symbol.Id,
        fn_lit: Func.Id,
    };

    const len = 1024;

    items: [len]Item = undefined,
    read: u32 = 0,
    write: u32 = 1,

    pub fn push(q: *Queue, item: Item) void {
        debug.assert((q.write + 1) % len != q.read, "analysis queue OOM");
        q.items[q.write] = item;
        q.write = (q.write + 1) % len;
    }

    pub fn pop(q: *Queue) Item {
        if ((q.read + 1) % len == q.write) return .empty;
        q.read = (q.read + 1) % len;
        return q.items[q.read];
    }
};

pub fn analyze(ctx: *Context, arena: *mem.Arena) void {
    const flusher = mem.Flusher.init(arena);
    defer flusher.flush();

    var item = ctx.analysis_q.pop();
    while (item != .empty) : (item = ctx.analysis_q.pop()) {
        switch (item) {
            .decl => |decl| {
                const symbol = ctx.symbol_table.get(decl);
                const file = ctx.getFile(symbol.file);

                const state = typed_lower.evalBlock(ctx, arena, symbol.file, symbol.value_inst);
                const result = state.results[@backingInt(symbol.value_inst)];

                if (symbol.type_inst != .none) {
                    const res = typed_lower.evalBlock(ctx, arena, symbol.file, symbol.type_inst);
                    const type_id = res.results[@backingInt(symbol.type_inst)].known.val.type;
                    if (type_id != result.known.type) @panic("TODO: handle type check failed");
                }

                switch (result.known.val) {
                    .fn_lit => {
                        const func = ctx.func_table.get(result.known.val.fn_lit);
                        if (func.status == .unchecked) {
                            ctx.analysis_q.push(.{ .fn_lit = result.known.val.fn_lit });
                            func.status = .{ .queued = state };
                        }
                    },
                    else => {},
                }

                const name_token = lexer.lexToken(file.contents, symbol.pos);
                const name_str = file.contents[name_token.start..name_token.end];
                debug.log("analyzed value: {s} = {}", .{ name_str, result });
            },
            .fn_lit => |lit| {
                const func = ctx.func_table.get(lit);
                debug.assert(func.status == .queued, "fn check item invalid status");

                const jump = typed_lower.lowerInst(func.status.queued, func.untyped_inst, .emit);
                debug.assert(jump.control == .none, "jump on emit mode lower");
                const fn_inst = func.status.queued.results[@backingInt(func.untyped_inst)].runtime;
                func.status = .{ .checked = fn_inst };
            },
            .empty => unreachable,
        }
    }
}
