const stdx = @import("stdx.zig");
const mem = stdx.mem;
const debug = stdx.debug;
const math = stdx.math;

const Context = @import("types.zig").Context;
const UntypedIr = @import("types.zig").UntypedIr;
const TypedIr = @import("types.zig").TypedIr;
const File = @import("types.zig").File;
const TypeLit = @import("types.zig").TypeLit;
const Constant = @import("types.zig").Constant;
const Symbol = @import("types.zig").Symbol;

const lexer = @import("lexer.zig");

const State = struct {
    arena: mem.Arena,
    ctx: *Context,
};

pub const Value = union(enum) {
    empty,
    type: Constant.Id,
    number: i64,
    boolean: bool,
    undef: void,
    fn_lit: UntypedIr.InstId,
};

pub const Queue = struct {
    pub const Item = union(enum) {
        empty,
        decl: struct {
            file: File.Id,
            symbol: Symbol.Id,
        },
        fn_lit: struct {
            flusher: mem.Flusher,

            file: File.Id,
            results: []Value,
            inst_id: UntypedIr.InstId,
        },
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
    const state = arena.pushStruct(State);
    state.* = .{
        .ctx = ctx,
        .arena = arena.subArena(1 * mem.MB),
    };

    var item = ctx.analysis_q.pop();
    while (item != .empty) : (item = ctx.analysis_q.pop()) {
        switch (item) {
            .decl => |decl| {
                const symbol = ctx.symbol_table.get(decl.symbol);
                if (symbol.type_inst != .none) {
                    @panic("TODO: handle type annotations of global decls");
                }

                var escaped = false;
                const flusher = mem.Flusher.init(&state.arena);
                defer if (!escaped) flusher.flush();

                const result = evaluate(state, symbol.file, symbol.value_inst);
                const val = result.results[@backingInt(result.break_val)];

                switch (val) {
                    .fn_lit => {
                        // TODO: queue it for analysis
                    },
                    else => {},
                }
                escaped = false;

                const file = ctx.getFile(symbol.file);
                const name_token = lexer.lexToken(file.contents, symbol.pos);
                const name_str = file.contents[name_token.start..name_token.end];
                debug.log("analyzed value: {s} = {}", .{ name_str, val });
            },
            .fn_lit => {},
            .empty => unreachable,
        }
    }
}

const EvalResult = struct {
    results: []Value,
    break_val: UntypedIr.InstId,
};

fn evaluate(state: *State, file_id: File.Id, block_id: UntypedIr.InstId) EvalResult {
    const file = state.ctx.getFile(file_id);
    const results = state.arena.pushArray(Value, file.untyped_ir.inst_count);

    // just for safety check ?
    for (results) |*r| r.* = .empty;

    const block = file.untyped_ir.getInst(block_id);

    debug.assert(block.tag == .comp_block, "evaluate not a comp block");
    for (block.data.block) |inst_id| {
        const inst = file.untyped_ir.getInst(inst_id);
        results[@backingInt(inst_id)] = switch (inst.tag) {
            .type_lit => blk: {
                const constant_id = state.ctx.constants.getOrAddId(.{
                    .tag = .type_lit,
                    .data = .{ .type = inst.data.type_lit },
                });
                break :blk .{ .type = constant_id };
            },
            .fn_type => blk: {
                const flusher1 = mem.Flusher.init(&state.arena);
                defer flusher1.flush();

                const ret = results[@backingInt(inst.data.fn_type.return_type)].type;
                const args = state.arena.pushArray(Constant.Id, inst.data.fn_type.arg_types.len);
                for (inst.data.fn_type.arg_types, 0..) |arg, i| {
                    args[i] = results[@backingInt(arg)].type;
                }

                const constant_id = state.ctx.constants.getOrAddId(.{
                    .tag = .fn_type,
                    .data = .{ .fn_type = .{ .ret = ret, .args = args } },
                });
                break :blk .{ .type = constant_id };
            },
            .num_lit => blk: {
                const num_token = lexer.lexToken(file.contents, inst.pos);
                debug.assert(num_token.tag == .num_literal, "num lit lexed token invalid");
                const num_str = file.contents[num_token.start..num_token.end];
                const num = math.parseInt(i64, num_str) catch @panic("TODO: handle invalid num");
                break :blk .{ .number = num };
            },
            .brk => {
                return .{
                    .results = results,
                    .break_val = inst.data.bin_op.rhs,
                };
            },
            .fn_lit => .{ .fn_lit = inst_id },

            else => @panic("TODO: eval other instructions"),
        };
    }

    @panic("Eval: compile block did not break");
}
