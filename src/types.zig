const stdx = @import("stdx.zig");
const mem = stdx.mem;
const math = stdx.math;
const debug = stdx.debug;

const lexer = @import("lexer.zig");

pub const Message = struct {
    pub const Severity = enum { info, warn, err };

    pub const Position = struct {
        file: File.Id,
        offset: u32,
    };

    severity: Severity,
    pos: Position,
    data: union(enum) {
        unexpected_token: struct {
            expected: lexer.Tag,
            found: lexer.Tag,
        },
        unexpected_operator: struct {
            found: lexer.Tag,
        },
        name_shadows_type: struct {
            found: TypeLit,
        },
        expected_binding_op: struct {
            found: lexer.Tag,
        },
        duplicate_decl: struct {
            original_pos: Position,
        },
    },
};

const max_messages = 2048;
const max_files = 2048;
const max_namespaces = 1024;

pub const Context = struct {
    intern_pool: InternPool = .{},

    files: [max_files]File = undefined,
    file_count: u32 = 1,

    namespaces: [max_namespaces]Namespace = undefined,
    namespace_count: u32 = 1,

    msgs: [max_messages]Message = undefined,
    msg_count: u32 = 0,

    symbol_table: Symbol.Table = .{},

    pub fn addMsg(ctx: *Context, msg: Message) void {
        ctx.msgs[ctx.msg_count] = msg;
        ctx.msg_count += 1;
    }

    pub fn addFile(ctx: *Context, file: File) File.Id {
        const result = ctx.file_count;
        ctx.file_count += 1;
        ctx.files[result] = file;
        return @fromBackingInt(result);
    }

    pub fn getFile(ctx: *Context, file_id: File.Id) *File {
        debug.assert(file_id != .none, "get none file");
        return &ctx.files[@backingInt(file_id)];
    }

    const namespace_size = 8 * mem.KB;
    pub fn addNamespace(ctx: *Context) Namespace.Id {
        const result = ctx.namespace_count;
        ctx.namespace_count += 1;
        ctx.namespaces[result] = .{ .arena = ctx.arena.subArena(namespace_size) };
        return @fromBackingInt(result);
    }

    pub fn getNamespace(ctx: *Context, ns_id: Namespace.Id) *Namespace {
        debug.assert(ns_id != .none, "get none file");
        return &ctx.namespaces[@backingInt(ns_id)];
    }
};

pub const File = struct {
    pub const Id = enum(u32) { none = 0, _ };

    path: []const u8,
    contents: []const u8,

    ast: *Ast,
    untyped_ir: *UntypedIr,
};

pub const Namespace = struct {
    pub const Id = enum(u32) { none = 0, _ };

    pub const Name = struct {
        intern_id: InternPool.Id,
        symbol_id: Symbol.Id,
        next: ?*Name,
    };

    const bucket_count = 1024;

    arena: mem.Arena,
    buckets: [bucket_count]?*Name = @splat(null),

    fn getSlot(ns: *Namespace, intern_id: InternPool.Id) *?*Name {
        const hash = @backingInt(intern_id) % bucket_count;
        var slot = &ns.buckets[hash];
        while (slot.*) |name| : (slot = &name.next) {
            if (name.intern_id == intern_id) break;
        }
        return slot;
    }

    /// returns exisiting symbol if it finds one, caller should check
    pub fn add(ns: *Namespace, intern_id: InternPool.Id, symbol_id: Symbol.Id) Symbol.Id {
        const slot = ns.getSlot(intern_id);
        if (slot.*) |name| return name.symbol_id;

        const name = ns.arena.pushStruct(Name);
        name.* = .{
            .intern_id = intern_id,
            .symbol_id = symbol_id,
            .next = null,
        };
        slot.* = name;
        return symbol_id;
    }

    pub fn find(ns: *Namespace, intern_id: InternPool.Id) Symbol.Id {
        const slot = ns.getSlot(intern_id);
        if (slot.*) |name| return name.symbol_id;
        return .none;
    }
};

pub const Symbol = struct {
    pub const Id = enum(u32) { none = 0, _ };

    pub const Table = struct {
        const max_symbols = 4096;

        symbols: [max_symbols]Symbol = undefined,
        next_id: u32 = 1,

        pub fn add(table: *Table, symbol: Symbol) Id {
            const result = table.next_id;
            table.next_id += 1;
            table.symbols[result] = symbol;
            return @fromBackingInt(result);
        }

        pub fn get(table: *Table, id: Id) *Symbol {
            debug.assert(id != .none, "get none symbol");
            return &table.symbols[@backingInt(id)];
        }
    };

    file: File.Id,
    ast_node: Ast.NodeId,

    type_inst: UntypedIr.InstId = .none,
    value_inst: UntypedIr.InstId = .none,
};

pub const TypeLit = enum(u32) {
    u8,
    u16,
    u32,
    u64,
    usize,

    i8,
    i16,
    i32,
    i64,
    isize,

    f32,
    f64,

    bool,
    void,
    noreturn,

    type_id,

    pub fn fromStr(str: []const u8) ?TypeLit {
        return if (mem.eql(str, "u8"))
            .u8
        else if (mem.eql(str, "u16"))
            .u16
        else if (mem.eql(str, "u32"))
            .u32
        else if (mem.eql(str, "u64"))
            .u64
        else if (mem.eql(str, "usize"))
            .usize
        else if (mem.eql(str, "i8"))
            .i8
        else if (mem.eql(str, "i16"))
            .i16
        else if (mem.eql(str, "i32"))
            .i32
        else if (mem.eql(str, "i64"))
            .i64
        else if (mem.eql(str, "isize"))
            .isize
        else if (mem.eql(str, "f32"))
            .f32
        else if (mem.eql(str, "f64"))
            .f64
        else if (mem.eql(str, "bool"))
            .bool
        else if (mem.eql(str, "void"))
            .void
        else if (mem.eql(str, "noreturn"))
            .noreturn
        else if (mem.eql(str, "type_id"))
            .type_id
        else
            null;
    }
};

pub const Ast = struct {
    pub const Tag = enum(u32) {
        file,

        identifier,

        bool_lit,
        undef_lit,
        num_lit,
        type_lit,

        fn_type,
        fn_lit,

        block,
        params,
        param,

        const_decl,
        var_decl,
        negate,

        add,
        subtract,
        mul,
        div,
        mod,
        assign,
    };

    pub const Node = struct {
        pos: u32,
        tag: Tag,
        data: union {
            block: []NodeId,

            identifier: struct { intern_id: InternPool.Id },

            type_lit: TypeLit,
            bool_lit: bool,

            fn_type: struct { args: NodeId, return_type: NodeId },
            fn_lit: struct { fn_type: NodeId, block: NodeId },

            param: struct { intern_id: InternPool.Id, type: NodeId },
            decl: struct { param: NodeId, value: NodeId },

            unary_op: NodeId,
            bin_op: struct { lhs: NodeId, rhs: NodeId },

            empty: void,
        },
    };

    pub fn allocNode(ast: *Ast, node: Node) NodeId {
        const packed_node: PackedNode = switch (node.tag) {
            .identifier => .{
                .pos = node.pos,
                .tag = node.tag,
                .lhs = @backingInt(node.data.identifier.intern_id),
                .rhs = 0,
            },

            .type_lit => .{
                .pos = node.pos,
                .tag = node.tag,
                .lhs = @backingInt(node.data.type_lit),
                .rhs = 0,
            },
            .bool_lit => .{
                .pos = node.pos,
                .tag = node.tag,
                .lhs = if (node.data.bool_lit) 1 else 0,
                .rhs = 0,
            },
            .num_lit, .undef_lit => .{
                .pos = node.pos,
                .tag = node.tag,
                .lhs = 0,
                .rhs = 0,
            },

            .fn_type => .{
                .pos = node.pos,
                .tag = node.tag,
                .lhs = @backingInt(node.data.fn_type.args),
                .rhs = @backingInt(node.data.fn_type.return_type),
            },
            .fn_lit => .{
                .pos = node.pos,
                .tag = node.tag,
                .lhs = @backingInt(node.data.fn_lit.fn_type),
                .rhs = @backingInt(node.data.fn_lit.block),
            },

            .block, .params, .file => blk: {
                const block = node.data.block;
                const extra_offset = ast.extra_count;
                for (block) |child| {
                    ast.extras[ast.extra_count] = @backingInt(child);
                    ast.extra_count += 1;
                }
                break :blk .{
                    .pos = node.pos,
                    .tag = node.tag,
                    .lhs = extra_offset,
                    .rhs = @intCast(block.len),
                };
            },

            .param => .{
                .pos = node.pos,
                .tag = node.tag,
                .lhs = @backingInt(node.data.param.intern_id),
                .rhs = @backingInt(node.data.param.type),
            },

            .const_decl, .var_decl => .{
                .pos = node.pos,
                .tag = node.tag,
                .lhs = @backingInt(node.data.decl.param),
                .rhs = @backingInt(node.data.decl.value),
            },

            .negate => .{
                .pos = node.pos,
                .tag = node.tag,
                .lhs = @backingInt(node.data.unary_op),
                .rhs = 0,
            },

            .add, .subtract, .mul, .div, .mod, .assign => .{
                .pos = node.pos,
                .tag = node.tag,
                .lhs = @backingInt(node.data.bin_op.lhs),
                .rhs = @backingInt(node.data.bin_op.rhs),
            },
        };
        const result = ast.node_count;
        ast.nodes[result] = packed_node;
        ast.node_count += 1;
        return @fromBackingInt(result);
    }

    pub fn getNode(ast: *Ast, id: NodeId) Node {
        const node = ast.nodes[@backingInt(id)];
        return .{
            .pos = node.pos,
            .tag = node.tag,
            .data = switch (node.tag) {
                .identifier => .{ .identifier = .{
                    .intern_id = @fromBackingInt(node.lhs),
                } },

                .bool_lit => .{ .bool_lit = node.lhs == 1 },
                .undef_lit => .{ .empty = {} },
                .type_lit => .{ .type_lit = @fromBackingInt(node.lhs) },

                .fn_type => .{ .fn_type = .{
                    .args = @fromBackingInt(node.lhs),
                    .return_type = @fromBackingInt(node.rhs),
                } },
                .fn_lit => .{ .fn_lit = .{
                    .fn_type = @fromBackingInt(node.lhs),
                    .block = @fromBackingInt(node.rhs),
                } },

                .block, .params, .file => blk: {
                    const first_node: [*]NodeId = @ptrCast(&ast.extras[node.lhs]);
                    break :blk .{ .block = first_node[0..node.rhs] };
                },

                .param => .{ .param = .{
                    .intern_id = @fromBackingInt(node.lhs),
                    .type = @fromBackingInt(node.rhs),
                } },

                .const_decl, .var_decl => .{ .decl = .{
                    .param = @fromBackingInt(node.lhs),
                    .value = @fromBackingInt(node.rhs),
                } },

                .negate => .{ .unary_op = @fromBackingInt(node.lhs) },

                .add, .subtract, .mul, .div, .mod, .assign => .{ .bin_op = .{
                    .lhs = @fromBackingInt(node.lhs),
                    .rhs = @fromBackingInt(node.rhs),
                } },

                .num_lit => .{ .empty = {} },
            },
        };
    }

    const PackedNode = struct {
        pos: u32,
        tag: Tag,
        lhs: u32,
        rhs: u32,
    };

    pub const NodeId = enum(u32) { none = 0, _ };
    pub const ExtraId = enum(u32) { none = 0, _ };

    const max_nodes = 8192;
    const max_extras = 4096;

    nodes: [max_nodes]PackedNode = undefined,
    node_count: u32 = 1,

    extras: [max_extras]u32 = undefined,
    extra_count: u32 = 1,
};

pub const UntypedIr = struct {
    pub const Tag = enum(u32) {
        reserved,

        comp_block,
        block,

        brk, // bin_op - block_id, value
        brk_implicit, // unary_op - block_id

        ret, // bin_op - fn_lit id, value
        ret_implicit, // unary_op - fn_lit id

        type_of,

        type_lit,
        num_lit,
        bool_lit,
        undef_lit,

        alloc,
        store,
        load,

        identifier,
        fn_lit,
        fn_arg,
        fn_type,

        add,
        subtract,
        mul,
        div,
        mod,
        assign,

        negate,
    };

    pub const Inst = struct {
        pos: u32,
        tag: Tag,
        data: union {
            empty: void,
            block: []InstId,

            type_lit: TypeLit,
            bool_lit: bool,

            fn_arg: struct { index: u32 },
            fn_lit: struct { type: InstId, body: []InstId },
            fn_type: struct { return_type: InstId, arg_types: []InstId },

            bin_op: struct { lhs: InstId, rhs: InstId },
            unary_op: InstId,
        },
    };

    const PackedInst = struct {
        tag: Tag,
        pos: u32,
        lhs: u32,
        rhs: u32,
    };

    fn packInst(ir: *UntypedIr, inst: Inst) PackedInst {
        return switch (inst.tag) {
            .block, .comp_block => blk: {
                const extra_offset = ir.extra_count;
                for (inst.data.block) |child| {
                    ir.extras[ir.extra_count] = @backingInt(child);
                    ir.extra_count += 1;
                }
                break :blk .{
                    .pos = inst.pos,
                    .tag = inst.tag,
                    .lhs = extra_offset,
                    .rhs = @intCast(inst.data.block.len),
                };
            },

            .reserved, .num_lit, .undef_lit, .identifier => .{
                .pos = inst.pos,
                .tag = inst.tag,
                .lhs = 0,
                .rhs = 0,
            },
            .bool_lit => .{
                .pos = inst.pos,
                .tag = inst.tag,
                .lhs = if (inst.data.bool_lit) 1 else 0,
                .rhs = 0,
            },
            .type_lit => .{
                .pos = inst.pos,
                .tag = inst.tag,
                .lhs = @backingInt(inst.data.type_lit),
                .rhs = 0,
            },

            .fn_lit => blk: {
                const extra_offset = ir.extra_count;
                ir.extras[ir.extra_count] = @backingInt(inst.data.fn_lit.type);
                ir.extra_count += 1;
                for (inst.data.fn_lit.body) |child| {
                    ir.extras[ir.extra_count] = @backingInt(child);
                    ir.extra_count += 1;
                }
                break :blk .{
                    .pos = inst.pos,
                    .tag = inst.tag,
                    .lhs = @intCast(inst.data.fn_lit.body.len),
                    .rhs = extra_offset,
                };
            },
            .fn_type => blk: {
                const extra_offset = ir.extra_count;
                ir.extras[ir.extra_count] = @backingInt(inst.data.fn_type.return_type);
                ir.extra_count += 1;

                for (inst.data.fn_type.arg_types) |child| {
                    ir.extras[ir.extra_count] = @backingInt(child);
                    ir.extra_count += 1;
                }

                break :blk .{
                    .pos = inst.pos,
                    .tag = inst.tag,
                    .lhs = @intCast(inst.data.fn_type.arg_types.len),
                    .rhs = extra_offset,
                };
            },
            .fn_arg => .{
                .pos = inst.pos,
                .tag = inst.tag,
                .lhs = inst.data.fn_arg.index,
                .rhs = 0,
            },

            .add, .subtract, .mul, .div, .mod, .alloc, .assign, .store, .brk, .ret => .{
                .pos = inst.pos,
                .tag = inst.tag,
                .lhs = @backingInt(inst.data.bin_op.lhs),
                .rhs = @backingInt(inst.data.bin_op.rhs),
            },

            .load, .type_of, .negate, .ret_implicit, .brk_implicit => .{
                .pos = inst.pos,
                .tag = inst.tag,
                .lhs = @backingInt(inst.data.unary_op),
                .rhs = 0,
            },
        };
    }

    fn unpackInst(ir: *UntypedIr, inst: PackedInst) Inst {
        return .{
            .pos = inst.pos,
            .tag = inst.tag,
            .data = switch (inst.tag) {
                .block, .comp_block => blk: {
                    const first_inst: [*]InstId = @ptrCast(&ir.extras[inst.lhs]);
                    break :blk .{ .block = first_inst[0..inst.rhs] };
                },

                .reserved, .num_lit, .identifier, .undef_lit => .{ .empty = {} },
                .bool_lit => .{ .bool_lit = inst.lhs == 1 },
                .type_lit => .{ .type_lit = @fromBackingInt(inst.lhs) },

                .fn_lit => blk: {
                    const body: [*]InstId = @ptrCast(&ir.extras[inst.rhs + 1]);
                    break :blk .{ .fn_lit = .{
                        .type = @fromBackingInt(ir.extras[inst.rhs]),
                        .body = body[0..inst.lhs],
                    } };
                },
                .fn_type => blk: {
                    const args: [*]InstId = @ptrCast(&ir.extras[inst.rhs + 1]);
                    break :blk .{ .fn_type = .{
                        .return_type = @fromBackingInt(ir.extras[inst.rhs]),
                        .arg_types = args[0..inst.lhs],
                    } };
                },
                .fn_arg => .{ .fn_arg = .{
                    .index = inst.lhs,
                } },

                .add, .subtract, .mul, .div, .mod, .assign, .alloc, .store, .brk, .ret => .{
                    .bin_op = .{
                        .lhs = @fromBackingInt(inst.lhs),
                        .rhs = @fromBackingInt(inst.rhs),
                    },
                },

                .load, .type_of, .negate, .ret_implicit, .brk_implicit => .{
                    .unary_op = @fromBackingInt(inst.lhs),
                },
            },
        };
    }

    pub const InstId = enum(u32) { none = 0, _ };
    pub const ExtraId = enum(u32) { none = 0, _ };

    const max_insts = 8192;
    const max_extras = 8192;

    insts: [max_insts]PackedInst = undefined,
    inst_count: u32 = 1,

    extras: [max_extras]u32 = undefined,
    extra_count: u32 = 1,

    pub fn getInst(ir: *UntypedIr, id: InstId) Inst {
        const inst = ir.insts[@backingInt(id)];
        return ir.unpackInst(inst);
    }

    pub fn overwriteInst(ir: *UntypedIr, id: InstId, inst: Inst) void {
        ir.insts[@backingInt(id)] = ir.packInst(inst);
    }

    pub fn allocInst(ir: *UntypedIr, inst: Inst) InstId {
        const result = ir.inst_count;
        ir.insts[result] = ir.packInst(inst);
        ir.inst_count += 1;
        return @fromBackingInt(result);
    }
};

pub const InternPool = struct {
    const bucket_count = 1024;
    const item_count = 4096;

    pub const Id = enum(u32) { none = 0, _ };

    buckets: [bucket_count]Id = @splat(.none),
    next: [item_count]Id = @splat(.none),

    strs: [item_count][]const u8 = undefined,
    str_count: u32 = 1,

    pub fn getOrCreateId(pool: *InternPool, str: []const u8) Id {
        const bucket = hash(str) % bucket_count;
        var slot = &pool.buckets[bucket];
        while (slot.* != .none) : (slot = &pool.next[@backingInt(slot.*)]) {
            if (mem.eql(pool.strs[@backingInt(slot.*)], str)) break;
        }
        if (slot.* == .none) {
            pool.strs[pool.str_count] = str;
            slot.* = @fromBackingInt(pool.str_count);
            pool.str_count += 1;
        }
        return slot.*;
    }

    pub fn getString(pool: *InternPool, id: Id) []const u8 {
        debug.assert(id != .none and @backingInt(id) < pool.str_count, "invalid intern id");
        return pool.strs[@backingInt(id)];
    }

    fn hash(str: []const u8) u64 {
        var result: math.Fnv = .{};
        result.roll(str);
        return result.hash;
    }
};
