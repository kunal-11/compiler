pub const mem = struct {
    pub const KB = 1 << 10;
    pub const MB = 1 << 20;
    pub const GB = 1 << 30;

    pub fn eql(a: []const u8, b: []const u8) bool {
        if (a.len != b.len) return false;
        for (a, b) |va, vb| {
            if (va != vb) return false;
        }
        return true;
    }

    pub fn alignUp(val: usize, alignment: usize) usize {
        return alignDown(val + alignment - 1, alignment);
    }

    pub fn alignDown(val: usize, alignment: usize) usize {
        debug.assert(math.isPow2(alignment), "alignment not power of 2");
        return val & ~(alignment - 1);
    }

    pub const Arena = struct {
        memory: []u8,
        used: usize = 0,

        pub fn subArena(arena: *Arena, len: usize) Arena {
            return .{ .memory = arena.pushArray(u8, len) };
        }

        pub fn pushStruct(arena: *Arena, T: type) *T {
            return @ptrCast(arena.pushBytes(@sizeOf(T), @alignOf(T)));
        }

        pub fn pushArray(arena: *Arena, T: type, len: usize) []T {
            return @ptrCast(arena.pushBytes(@sizeOf(T) * len, @alignOf(T)));
        }

        fn pushBytes(arena: *Arena, len: usize, comptime alignment: usize) []align(alignment) u8 {
            const ptr = @intFromPtr(arena.memory.ptr + arena.used);
            const align_offset = alignUp(ptr, alignment) - ptr;
            arena.used += align_offset + len;
            debug.assert(arena.used <= arena.memory.len, "arena OOM");
            return @alignCast(arena.memory[arena.used - len .. arena.used]);
        }
    };

    pub const Flusher = struct {
        arena: *Arena,
        base: usize,

        pub fn init(arena: *Arena) Flusher {
            return .{ .arena = arena, .base = arena.used };
        }

        pub fn flush(flusher: Flusher) void {
            flusher.arena.used = flusher.base;
        }
    };
};

pub const math = struct {
    pub fn isPow2(val: anytype) bool {
        return val & (val - 1) == 0;
    }

    pub const Fnv = struct {
        const init = 14695981039346656037;
        const multiplier = 1099511628211;

        hash: u64 = init,

        pub fn roll(fnv: *Fnv, val: []const u8) void {
            for (val) |char| {
                fnv.hash ^= char;
                fnv.hash *%= multiplier;
            }
        }

        pub fn roll32(fnv: *Fnv, val: u32) void {
            var bytes: [4]u8 = @bitCast(val);
            fnv.roll(&bytes);
        }
    };
};

const std = @import("std");
pub const debug = struct {
    pub fn assert(ok: bool, msg: []const u8) void {
        if (!ok) {
            @panic(msg);
        }
    }

    pub const log = std.log.debug;
    pub const print = std.debug.print;
};
