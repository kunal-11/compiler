const stdx = @import("stdx.zig");
const mem = stdx.mem;
const debug = stdx.debug;

const lexer = @import("lexer.zig");

const Context = @import("types.zig").Context;
const File = @import("types.zig").File;
const Ast = @import("types.zig").Ast;
const InternPool = @import("types.zig").InternPool;
const Type = @import("types.zig").Type;

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
    ctx: *Context,
    file_id: File.Id,
    ast: *Ast,
    tokens: TokenCache,

    node_stack: [8192]Ast.NodeId = undefined,
    node_count: u32 = 0,
};

const ParseError = error{ UnexpectedToken, IntrinsicShadowing, ExpectedExpression };

pub fn parseFile(ctx: *Context, arena: *mem.Arena, file_id: File.Id) Ast.NodeId {
    const file = ctx.getFile(file_id);

    const flusher = mem.Flusher.init(arena);
    defer flusher.flush();

    const state = arena.pushStruct(State);
    state.* = .{
        .ctx = ctx,
        .file_id = file_id,
        .ast = file.ast,
        .tokens = .{ .buf = file.contents },
    };

    while (state.tokens.peek().tag != .eof) {
        state.node_stack[state.node_count] = parseDecl(state) catch {
            skipStatement(state);
            const token = state.tokens.peek();
            if (token.tag == .close_brace) {
                state.ctx.addMsg(.{
                    .pos = .{ .file = state.file_id, .offset = token.start },
                    .severity = .err,
                    .data = .{ .unexpected_token = .{
                        .expected = .identifier,
                    } },
                });
                state.tokens.advance();
            }
            continue;
        };
        state.node_count += 1;
    }

    return state.ast.allocNode(.{
        .pos = 0,
        .tag = .file,
        .data = .{ .block = state.ast.allocList(state.node_stack[0..state.node_count]) },
    });
}

fn parseDecl(state: *State) ParseError!Ast.NodeId {
    const identifier = try expect(state, .identifier);
    const str = state.tokens.str(identifier);
    _ = try expect(state, .colon);

    const type_node = switch (state.tokens.peek().tag) {
        .colon, .equals => .none,
        else => parseType(state) catch .poison,
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
                .data = .expected_binding_op,
            });
            return error.UnexpectedToken;
        },
    };
    state.tokens.advance();

    const value_node = parseExpression(state, min_bind_power) catch .poison;

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
    const node_marker = state.node_count;
    defer state.node_count = node_marker;

    const open_token = try expect(state, .open_brace);
    while (true) {
        switch (state.tokens.peek().tag) {
            .eof, .close_brace => break,
            else => {
                state.node_stack[state.node_count] = parseStatement(state) catch {
                    skipStatement(state);
                    continue;
                };
                state.node_count += 1;
            },
        }
    }
    _ = try expect(state, .close_brace);

    return state.ast.allocNode(.{
        .pos = open_token.start,
        .tag = .block,
        .data = .{ .block = state.ast.allocList(state.node_stack[node_marker..state.node_count]) },
    });
}

fn parseStatement(state: *State) ParseError!Ast.NodeId {
    const token = state.tokens.peek();
    switch (token.tag) {
        .identifier => if (state.tokens.peek2().tag == .colon) return try parseDecl(state),
        .key_return => {
            state.tokens.advance();
            const expr = if (state.tokens.peek().tag == .semicolon)
                .none
            else
                try parseExpression(state, min_bind_power);

            const result = state.ast.allocNode(.{
                .pos = token.start,
                .tag = .ret,
                .data = .{ .unary_op = expr },
            });
            _ = try expect(state, .semicolon);
            return result;
        },
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
        else => {
            state.ctx.addMsg(.{
                .severity = .err,
                .pos = .{ .file = state.file_id, .offset = token.start },
                .data = .expected_type,
            });
            return error.ExpectedExpression;
        },
    };
}

const max_fn_args = 256;
fn parseFnType(state: *State) ParseError!Ast.NodeId {
    const fn_token = try expect(state, .key_fn);

    const node_marker = state.node_count;
    defer state.node_count = node_marker;

    const paren_node = try expect(state, .open_paren);
    while (state.tokens.peek().tag == .identifier) {
        state.node_stack[state.node_count] = try parseFnArg(state);
        state.node_count += 1;

        if (state.tokens.peek().tag == .comma) {
            state.tokens.advance();
        } else break;
    }
    _ = try expect(state, .close_paren);

    const return_type = try parseType(state);

    const args_node = state.ast.allocNode(.{
        .pos = paren_node.start,
        .tag = .params,
        .data = .{ .block = state.ast.allocList(state.node_stack[node_marker..state.node_count]) },
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

fn parseFnArg(state: *State) ParseError!Ast.NodeId {
    const identifier = try expect(state, .identifier);
    const str = state.tokens.str(identifier);
    _ = try expect(state, .colon);

    const type_node = parseType(state) catch .poison;

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
    const token = state.tokens.peek();
    var result = switch (token.tag) {
        .minus => try parseUnaryOp(state, bind_power),
        .key_fn => try parseFnTypeOrLiteral(state),
        .identifier => try parseIdentifier(state),
        .key_undefined => parseUndefLit(state),
        .key_false, .key_true => parseBoolLit(state),
        .num_literal => parseNumLit(state),
        else => {
            state.ctx.addMsg(.{
                .severity = .err,
                .pos = .{ .file = state.file_id, .offset = token.start },
                .data = .expected_expression,
            });
            return error.ExpectedExpression;
        },
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
            .data = .expected_operator,
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

fn parseNumLit(state: *State) Ast.NodeId {
    const token = state.tokens.peek();
    debug.assert(token.tag == .num_literal, "parse invalid num literal");
    state.tokens.advance();
    return state.ast.allocNode(.{
        .pos = token.start,
        .tag = .num_lit,
        .data = .{ .empty = {} },
    });
}

fn parseUndefLit(state: *State) Ast.NodeId {
    const token = state.tokens.peek();
    debug.assert(token.tag == .key_undefined, "parse invalid undef literal");
    state.tokens.advance();
    return state.ast.allocNode(.{
        .pos = token.start,
        .tag = .undef_lit,
        .data = .{ .empty = {} },
    });
}

fn parseBoolLit(state: *State) Ast.NodeId {
    const token = state.tokens.peek();
    debug.assert(token.tag == .key_false or token.tag == .key_true, "parse invalid bool lit");
    state.tokens.advance();
    return state.ast.allocNode(.{
        .pos = token.start,
        .tag = .bool_lit,
        .data = .{ .bool_lit = token.tag == .key_true },
    });
}

fn parseIdentifier(state: *State) ParseError!Ast.NodeId {
    const token = try expect(state, .identifier);
    const str = state.tokens.str(token);
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
        } },
    });
    return error.UnexpectedToken;
}
