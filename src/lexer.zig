const stdx = @import("stdx.zig");
const mem = stdx.mem;
const debug = stdx.debug;

pub const Tag = enum {
    eof,
    invalid,

    identifier,

    key_fn,
    key_return,

    key_true,
    key_false,

    key_undefined,

    num_literal,

    open_paren,
    close_paren,

    open_brace,
    close_brace,

    open_bracket,
    close_bracket,

    dot,

    plus,
    minus,
    mul,
    div,
    mod,

    comma,
    semicolon,
    colon,
    equals,
};

pub const Token = struct {
    tag: Tag,
    start: u32,
    end: u32,
};

const State = enum { start, word, num, err };

pub fn lexToken(buf: []const u8, pos: u32) Token {
    var state = State.start;
    var start: u32 = 0;
    var cursor = pos;
    while (cursor <= buf.len) {
        const char = if (cursor == buf.len) 0 else buf[cursor];
        switch (state) {
            .start => switch (char) {
                'a'...'z', 'A'...'Z', '_' => {
                    state = .word;
                    start = cursor;
                },
                '0'...'9' => {
                    state = .num;
                    start = cursor;
                },

                0, ' ', '\r', '\n', '\t' => {},

                '+' => return singleCharToken(.plus, cursor),
                '-' => return singleCharToken(.minus, cursor),
                '*' => return singleCharToken(.mul, cursor),
                '/' => return singleCharToken(.div, cursor),
                '%' => return singleCharToken(.mod, cursor),

                ':' => return singleCharToken(.colon, cursor),
                ';' => return singleCharToken(.semicolon, cursor),
                '=' => return singleCharToken(.equals, cursor),
                ',' => return singleCharToken(.comma, cursor),
                '.' => return singleCharToken(.dot, cursor),

                '(' => return singleCharToken(.open_paren, cursor),
                ')' => return singleCharToken(.close_paren, cursor),

                '{' => return singleCharToken(.open_brace, cursor),
                '}' => return singleCharToken(.close_brace, cursor),

                '[' => return singleCharToken(.open_bracket, cursor),
                ']' => return singleCharToken(.close_bracket, cursor),

                else => {
                    state = .err;
                    start = cursor;
                },
            },
            .word => switch (char) {
                'a'...'z', 'A'...'Z', '0'...'9', '_' => {},
                else => return parseWordToken(buf, start, cursor),
            },
            .num => switch (char) {
                '0'...'9', '.', 'x', 'a'...'f' => {},
                else => return .{
                    .tag = .num_literal,
                    .start = start,
                    .end = cursor,
                },
            },
            .err => switch (char) {
                0, ' ', '\r', '\n', '\t', ';', '{', '(' => return .{
                    .tag = .invalid,
                    .start = start,
                    .end = cursor,
                },
                else => {},
            },
        }
        cursor += 1;
    }
    debug.assert(state == .start, "file lexing ended on invalid state");
    return .{
        .tag = .eof,
        .start = @intCast(buf.len),
        .end = @intCast(buf.len),
    };
}

fn parseWordToken(buf: []const u8, start: u32, end: u32) Token {
    const word = buf[start..end];
    const tag: Tag = if (mem.eql(word, "fn"))
        .key_fn
    else if (mem.eql(word, "true"))
        .key_true
    else if (mem.eql(word, "false"))
        .key_false
    else if (mem.eql(word, "undefined"))
        .key_undefined
    else if (mem.eql(word, "return"))
        .key_return
    else
        .identifier;
    return .{
        .tag = tag,
        .start = start,
        .end = end,
    };
}

fn singleCharToken(tag: Tag, cursor: u32) Token {
    return .{
        .tag = tag,
        .start = cursor,
        .end = cursor + 1,
    };
}
