const stdx = @import("stdx.zig");
const mem = stdx.mem;

const lexer = @import("lexer.zig");

const Context = @import("types.zig").Context;
const File = @import("types.zig").File;
const Ast = @import("types.zig").Ast;
const InternPool = @import("types.zig").InternPool;
const Intrinsic = @import("types.zig").Intrinsic;

const TokenCache = struct {
    buf: []const u8,
    cursor: u32 = 0,

    t1: ?lexer.Token = null,
    t2: ?lexer.Token = null,

    fn peek(cache: *TokenCache) lexer.Token {
        if (cache.t1 == null) {
            cache.t1 = lexer.lexToken(cache.buf, cache.cursor);
        }
        return cache.t1.?;
    }

    fn peek2(cache: *TokenCache) lexer.Token {
        const token = cache.peek();
        if (cache.t2 == null) {
            cache.t2 = lexer.lexToken(cache.buf, token.end);
        }
        return cache.t2.?;
    }

    fn advance(cache: *TokenCache) void {
        const token = cache.peek();
        cache.cursor = token.end;
        cache.t1 = cache.t2;
        cache.t2 = null;
    }

    fn str(cache: *TokenCache, token: lexer.Token) []const u8 {
        return cache.buf[token.start..token.end];
    }
};

const min_bind_power: u32 = 0;
fn opPrecedence(tag: lexer.Tag, prefix: bool) u32 {
    return if (prefix) switch (tag) {
        .minus => 4,
        else => @panic("token not an prefix operator"),
    } else switch (tag) {
        .plus, .minus => 2,
        .mul, .div, .mod => 3,
        else => @panic("token not an infix or postfix operator"),
    };
}

const State = struct {
    arena: mem.Arena,
    ctx: *Context,
    file_id: File.Id,
    ast: *Ast,
    tokens: TokenCache,
};

const ParseError = error{ UnexpectedToken, IntrinsicShadowing };

const max_file_decls = 2048;
pub fn parseFile(ctx: *Context, file_id: File.Id) []Ast.NodeId {
    const decls = ctx.arena.pushArray(Ast.NodeId, max_file_decls);
    var decl_count: u32 = 0;

    const flusher = mem.Flusher.init(&ctx.arena);
    defer flusher.flush();

    const file = ctx.getFile(file_id);
    var state = State{
        .ctx = ctx,
        .file_id = file_id,
        .ast = file.ast,
        .arena = ctx.arena.subArena(8 * mem.MB),
        .tokens = .{ .buf = file.contents },
    };

    while (state.tokens.peek().tag != .eof) {
        decls[decl_count] = parseDecl(&state) catch {
            skipStatement(&state);
            if (state.tokens.peek().tag == .close_brace)
                @panic("TODO: handle dangling close brace");
            continue;
        };
        decl_count += 1;
    }

    return decls[0..decl_count];
}

fn skipStatement(state: *State) void {
    var opened_braces: u32 = 0;
    while (true) {
        const token = state.tokens.peek();
        switch (token.tag) {
            .semicolon => {
                state.tokens.advance();
                if (opened_braces == 0) break;
            },
            .open_brace => {
                opened_braces += 1;
                state.tokens.advance();
            },
            .close_brace => if (opened_braces > 0) {
                opened_braces -= 1;
                state.tokens.advance();
            } else break,
            .eof => break,
            else => state.tokens.advance(),
        }
    }
}

fn parseDecl(state: *State) ParseError!Ast.NodeId {
    const identifier = try expect(state, .identifier);
    const str = state.tokens.str(identifier);
    if (Intrinsic.fromStr(str)) |intrinsic| {
        state.ctx.addMsg(.{
            .severity = .err,
            .pos = .{ .file = state.file_id, .offset = identifier.start },
            .data = .{ .name_shadows_intrinsic = .{ .found = intrinsic } },
        });
        return error.IntrinsicShadowing;
    }
    _ = try expect(state, .colon);

    const type_node = switch (state.tokens.peek().tag) {
        .colon, .equals => .none,
        else => try parseType(state),
    };

    const intern_id = state.ctx.intern_pool.getOrCreateId(str);
    const param_node = state.ast.allocNode(.{
        .pos = identifier.start,
        .tag = .param,
        .data = .{ .param = .{
            .intern_id = intern_id,
            .type = type_node,
        } },
    });

    const op_token = state.tokens.peek();
    const is_const = switch (op_token.tag) {
        .colon => true,
        .equals => false,
        else => {
            state.ctx.addMsg(.{
                .pos = .{ .file = state.file_id, .offset = op_token.start },
                .severity = .err,
                .data = .{
                    .expected_binding_op = .{ .found = op_token.tag },
                },
            });
            return error.UnexpectedToken;
        },
    };
    state.tokens.advance();

    const value_node = try parseExpression(state, min_bind_power);

    _ = try expect(state, .semicolon);

    return state.ast.allocNode(.{
        .pos = op_token.start,
        .tag = if (is_const) .const_decl else .var_decl,
        .data = .{ .decl = .{
            .param = param_node,
            .value = value_node,
        } },
    });
}

const max_block_statements = 8192;
fn parseBlock(state: *State) ParseError!Ast.NodeId {
    const flusher = mem.Flusher.init(&state.arena);
    defer flusher.flush();

    const scratch = state.arena.pushArray(Ast.NodeId, max_block_statements);
    var node_count: u32 = 0;

    const open_token = try expect(state, .open_brace);
    while (true) {
        switch (state.tokens.peek().tag) {
            .eof, .close_brace => break,
            else => {
                scratch[node_count] = parseStatement(state) catch {
                    skipStatement(state);
                    continue;
                };
                node_count += 1;
            },
        }
    }
    _ = try expect(state, .close_brace);

    return state.ast.allocNode(.{
        .pos = open_token.start,
        .tag = .block,
        .data = .{ .block = scratch[0..node_count] },
    });
}

fn parseStatement(state: *State) ParseError!Ast.NodeId {
    switch (state.tokens.peek().tag) {
        .identifier => if (state.tokens.peek2().tag == .colon) return try parseDecl(state),
        else => {},
    }

    var result = try parseExpression(state, min_bind_power);
    if (state.tokens.peek().tag == .equals) {
        const eq_token = try expect(state, .equals);
        const rhs = try parseExpression(state, min_bind_power);
        result = state.ast.allocNode(.{
            .pos = eq_token.start,
            .tag = .assign,
            .data = .{ .bin_op = .{
                .lhs = result,
                .rhs = rhs,
            } },
        });
    }
    _ = try expect(state, .semicolon);
    return result;
}

fn parseType(state: *State) ParseError!Ast.NodeId {
    const token = state.tokens.peek();
    return switch (token.tag) {
        // TODO: change this to type expr if we allow type gen macros
        .identifier => try parseIdentifier(state),
        .key_fn => try parseFnType(state),
        else => @panic("TODO"),
    };
}

const max_fn_args = 256;
fn parseFnType(state: *State) ParseError!Ast.NodeId {
    const fn_token = try expect(state, .key_fn);

    const flusher = mem.Flusher.init(&state.arena);
    defer flusher.flush();

    const arg_nodes = state.arena.pushArray(Ast.NodeId, max_fn_args);
    var arg_count: u32 = 0;

    const paren_node = try expect(state, .open_paren);
    while (state.tokens.peek().tag == .identifier) {
        arg_nodes[arg_count] = try parseParam(state);
        arg_count += 1;

        if (state.tokens.peek().tag == .comma) {
            state.tokens.advance();
        } else break;
    }
    _ = try expect(state, .close_paren);

    const return_type = try parseType(state);

    const args_node = state.ast.allocNode(.{
        .pos = paren_node.start,
        .tag = .params,
        .data = .{ .block = arg_nodes[0..arg_count] },
    });

    return state.ast.allocNode(.{
        .pos = fn_token.start,
        .tag = .fn_type,
        .data = .{ .fn_type = .{
            .args = args_node,
            .return_type = return_type,
        } },
    });
}

fn parseParam(state: *State) ParseError!Ast.NodeId {
    const identifier = try expect(state, .identifier);
    const str = state.tokens.str(identifier);
    if (Intrinsic.fromStr(str)) |intrinsic| {
        state.ctx.addMsg(.{
            .severity = .err,
            .pos = .{ .file = state.file_id, .offset = identifier.start },
            .data = .{ .name_shadows_intrinsic = .{ .found = intrinsic } },
        });
        return error.IntrinsicShadowing;
    }
    _ = try expect(state, .colon);

    const type_node = try parseType(state);

    const intern_id = state.ctx.intern_pool.getOrCreateId(str);
    return state.ast.allocNode(.{
        .pos = identifier.start,
        .tag = .param,
        .data = .{ .param = .{
            .intern_id = intern_id,
            .type = type_node,
        } },
    });
}

fn parseExpression(state: *State, bind_power: u32) ParseError!Ast.NodeId {
    var result = switch (state.tokens.peek().tag) {
        .minus => try parseUnaryOp(state, bind_power),
        .key_fn => try parseFnTypeOrLiteral(state),
        .num_literal => try parseNumLit(state),
        .identifier => try parseIdentifier(state),
        else => @panic("TODO: handle other kinds of expressions"),
    };

    while (true) {
        result = switch (state.tokens.peek().tag) {
            .plus, .minus, .mul, .div, .mod => blk: {
                const node = try parseInfixOp(state, result, bind_power);
                if (node == .none) break;
                break :blk node;
            },
            .dot => @panic("TODO: handle postfix operators"),
            else => break,
        };
    }
    return result;
}

fn parseUnaryOp(state: *State, parent_bind_power: u32) ParseError!Ast.NodeId {
    const token = state.tokens.peek();
    const bind_power = opPrecedence(token.tag, true);

    // TODO: better handling of nested unary ops ?
    if (bind_power < parent_bind_power) {
        state.ctx.addMsg(.{
            .severity = .err,
            .pos = .{ .file = state.file_id, .offset = token.start },
            .data = .{ .unexpected_operator = .{ .found = token.tag } },
        });
        return error.UnexpectedToken;
    }
    state.tokens.advance();

    const expr_node = try parseExpression(state, bind_power);
    return state.ast.allocNode(.{
        .pos = token.start,
        .tag = .negate,
        .data = .{ .unary_op = expr_node },
    });
}

fn parseInfixOp(state: *State, lhs: Ast.NodeId, parent_bind_power: u32) ParseError!Ast.NodeId {
    const token = state.tokens.peek();
    const bind_power = opPrecedence(token.tag, false);
    if (bind_power <= parent_bind_power) return .none;
    state.tokens.advance();

    const rhs = try parseExpression(state, bind_power);
    const tag: Ast.Tag = switch (token.tag) {
        .plus => .add,
        .minus => .subtract,
        .mul => .mul,
        .div => .div,
        .mod => .mod,
        else => @panic("unexpected operator"),
    };

    return state.ast.allocNode(.{
        .pos = token.start,
        .tag = tag,
        .data = .{ .bin_op = .{
            .lhs = lhs,
            .rhs = rhs,
        } },
    });
}

fn parseFnTypeOrLiteral(state: *State) ParseError!Ast.NodeId {
    const pos = state.tokens.peek().start;
    const type_node = try parseFnType(state);
    if (state.tokens.peek().tag == .open_brace) {
        const block_node = try parseBlock(state);
        return state.ast.allocNode(.{
            .pos = pos,
            .tag = .fn_lit,
            .data = .{ .fn_lit = .{
                .fn_type = type_node,
                .block = block_node,
            } },
        });
    }
    return type_node;
}

fn parseNumLit(state: *State) ParseError!Ast.NodeId {
    const token = try expect(state, .num_literal);
    return state.ast.allocNode(.{
        .pos = token.start,
        .tag = .num_lit,
        .data = .{ .empty = {} },
    });
}

fn parseIdentifier(state: *State) ParseError!Ast.NodeId {
    const token = try expect(state, .identifier);
    const str = state.tokens.str(token);
    if (Intrinsic.fromStr(str)) |intrinsic| {
        return state.ast.allocNode(.{
            .pos = token.start,
            .tag = .intrinsic,
            .data = .{ .intrinsic = intrinsic },
        });
    }
    const intern_id = state.ctx.intern_pool.getOrCreateId(str);
    return state.ast.allocNode(.{
        .pos = token.start,
        .tag = .identifier,
        .data = .{ .identifier = .{ .intern_id = intern_id } },
    });
}

fn expect(state: *State, tag: lexer.Tag) ParseError!lexer.Token {
    const token = state.tokens.peek();
    if (token.tag == tag) {
        state.tokens.advance();
        return token;
    }
    state.ctx.addMsg(.{
        .severity = .err,
        .pos = .{ .file = state.file_id, .offset = token.start },
        .data = .{ .unexpected_token = .{
            .expected = tag,
            .found = token.tag,
        } },
    });
    return error.UnexpectedToken;
}
