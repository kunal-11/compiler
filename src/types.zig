const stdx = @import("stdx.zig");
const mem = stdx.mem;
const math = stdx.math;
const debug = stdx.debug;

const lexer = @import("lexer.zig");
const analyzer = @import("analyzer.zig");

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

pub const Context = struct {
    const max_messages = 2048;
    const max_files = 2048;
    const max_namespaces = 1024;

    intern_pool: InternPool = .{},

    files: [max_files]File = undefined,
    file_count: u32 = 1,

    namespaces: [max_namespaces]Namespace = undefined,
    namespace_count: u32 = 1,

    msgs: [max_messages]Message = undefined,
    msg_count: u32 = 0,

    symbol_table: Symbol.Table = .{},
    analysis_q: analyzer.Queue = .{},
    constants: Constant.Pool = .{},

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
    pub fn addNamespace(ctx: *Context, arena: *mem.Arena) Namespace.Id {
        const result = ctx.namespace_count;
        ctx.namespace_count += 1;
        ctx.namespaces[result] = .{ .arena = arena.subArena(namespace_size) };
        return @fromBackingInt(result);
    }

    pub fn getNamespace(ctx: *Context, ns_id: Namespace.Id) *Namespace {
        debug.assert(ns_id != .none, "get none file");
        return &ctx.namespaces[@backingInt(ns_id)];
    }
};

pub const File = struct {
    pub const Id = enum(u32) { none = 0, _ };

    arena: mem.Arena,
    path: []const u8,
    contents: []const u8,

    ast: *Ast,
    untyped_ir: *UntypedIr,

    analysis: []analyzer.Value,
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

    pub const AddResult = union(enum) {
        success,
        duplicate: Symbol.Id,
    };

    pub fn add(ns: *Namespace, intern_id: InternPool.Id, symbol_id: Symbol.Id) AddResult {
        const slot = ns.getSlot(intern_id);
        if (slot.*) |name| return .{ .duplicate = name.symbol_id };

        const name = ns.arena.pushStruct(Name);
        name.* = .{
            .intern_id = intern_id,
            .symbol_id = symbol_id,
            .next = null,
        };
        slot.* = name;
        return .success;
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
            debug.assert(symbol.value_inst != .none, "symbol value cannot be none");
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
    pos: u32,
    type_inst: UntypedIr.InstId = .none,
    value_inst: UntypedIr.InstId,
    tag: enum { variable, constant },
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

    comp_int,
    comp_float,

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
        else if (mem.eql(str, "comp_int"))
            .comp_int
        else if (mem.eql(str, "comp_float"))
            .comp_float
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

        ret,

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

            .negate, .ret => .{
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

                .negate, .ret => .{ .unary_op = @fromBackingInt(node.lhs) },

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

        ret, // unary_op - value
        ret_implicit, // unary_op - fn_lit id

        type_of,

        global_ptr,
        global_val,

        type_lit,
        num_lit,
        bool_lit,
        undef_lit,

        alloc,
        store,
        load,

        fn_lit,
        fn_arg,
        fn_type,

        add,
        subtract,
        mul,
        div,
        mod,

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

            global_ref: InternPool.Id,

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

            .global_ptr, .global_val => .{
                .pos = inst.pos,
                .tag = inst.tag,
                .lhs = @backingInt(inst.data.global_ref),
                .rhs = 0,
            },

            .reserved, .num_lit, .undef_lit => .{
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

            .add, .subtract, .mul, .div, .mod, .alloc, .store, .brk => .{
                .pos = inst.pos,
                .tag = inst.tag,
                .lhs = @backingInt(inst.data.bin_op.lhs),
                .rhs = @backingInt(inst.data.bin_op.rhs),
            },

            .load, .type_of, .negate, .ret, .ret_implicit, .brk_implicit => .{
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

                .global_ptr, .global_val => .{ .global_ref = @fromBackingInt(inst.lhs) },

                .reserved, .num_lit, .undef_lit => .{ .empty = {} },
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

                .add, .subtract, .mul, .div, .mod, .alloc, .store, .brk => .{
                    .bin_op = .{
                        .lhs = @fromBackingInt(inst.lhs),
                        .rhs = @fromBackingInt(inst.rhs),
                    },
                },

                .load, .type_of, .negate, .ret, .ret_implicit, .brk_implicit => .{
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
        debug.assert(id != .none, "get none untyped inst");
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

pub const TypedIr = struct {
    pub const Tag = enum(u32) {
        arg,

        constant,
        add,
    };

    pub const InstId = enum(u32) { none = 0, _ };

    pub const Inst = struct {
        pos: u32,
        tag: Tag,
        data: union {
            arg: struct { index: u32, type: Constant.Id },

            constant: Constant.Id,

            bin_op: struct { lhs: InstId, rhs: InstId },
        },
    };

    const PackedInst = struct {
        pos: u32,
        tag: Tag,
        lhs: u32,
        rhs: u32,
    };

    fn packInst(ir: *TypedIr, inst: Inst) PackedInst {
        _ = ir;
        return switch (inst.tag) {
            .arg => .{
                .pos = inst.pos,
                .tag = inst.tag,
                .lhs = inst.data.arg.index,
                .rhs = @backingInt(inst.data.arg.type),
            },

            .constant => .{
                .pos = inst.pos,
                .tag = inst.tag,
                .lhs = @backingInt(inst.data.constant),
                .rhs = 0,
            },

            .add => .{
                .pos = inst.pos,
                .tag = inst.tag,
                .lhs = @backingInt(inst.data.bin_op.lhs),
                .rhs = @backingInt(inst.data.bin_op.rhs),
            },
        };
    }

    fn unpackInst(ir: *TypedIr, inst: PackedInst) Inst {
        _ = ir;
        return .{
            .pos = inst.pos,
            .tag = inst.tag,
            .data = switch (inst.tag) {
                .arg => .{ .arg = .{
                    .index = inst.lhs,
                    .type = @fromBackingInt(inst.rhs),
                } },
                .constant => .{ .constant = @fromBackingInt(inst.lhs) },
                .add => .{ .bin_op = .{
                    .lhs = @fromBackingInt(inst.lhs),
                    .rhs = @fromBackingInt(inst.rhs),
                } },
            },
        };
    }

    const max_insts = 8192;

    insts: [max_insts]PackedInst = undefined,
    inst_count: u32 = 1,

    pub fn getInst(ir: *TypedIr, id: InstId) Inst {
        debug.assert(id != .none, "get none typed inst");
        const inst = ir.insts[@backingInt(id)];
        return ir.unpackInst(inst);
    }

    pub fn allocInst(ir: *TypedIr, inst: Inst) InstId {
        const result = ir.inst_count;
        ir.insts[result] = ir.packInst(inst);
        ir.inst_count += 1;
        return @fromBackingInt(result);
    }
};

pub const Constant = struct {
    pub const Tag = enum(u8) {
        type_lit,
        fn_type,
    };

    tag: Tag,
    data: union {
        type_lit: TypeLit,
        fn_type: struct { ret: Id, args: []Id },
    },

    fn hash(c: Constant) u64 {
        var fnv = math.Fnv{};
        fnv.roll(&.{@backingInt(c.tag)});
        switch (c.tag) {
            .type_lit => fnv.roll32(@backingInt(c.data.type_lit)),
            .fn_type => {
                fnv.roll32(@backingInt(c.data.fn_type.ret));
                for (c.data.fn_type.args) |arg| {
                    fnv.roll32(@backingInt(arg));
                }
            },
        }
        return fnv.hash;
    }

    fn eql(c1: Constant, c2: Constant) bool {
        if (c1.tag != c2.tag) return false;
        return switch (c1.tag) {
            .type_lit => c1.data.type_lit == c2.data.type_lit,
            .fn_type => blk: {
                if (c1.data.fn_type.ret != c2.data.fn_type.ret or
                    c1.data.fn_type.args.len != c2.data.fn_type.args.len)
                {
                    break :blk false;
                }

                for (0..c1.data.fn_type.args.len) |arg_i| {
                    if (c1.data.fn_type.args[arg_i] != c2.data.fn_type.args[arg_i]) {
                        break :blk false;
                    }
                }

                break :blk true;
            },
        };
    }

    pub const Id = enum(u32) { none = 0, _ };

    pub const Pool = struct {
        const max_constants = 4096;
        const max_extras = 2048;
        const max_buckets = 1024;

        buckets: [max_buckets]Id = @splat(.none),
        next: [max_constants]Id = @splat(.none),

        constants: [max_constants]Packed = undefined,
        next_id: u32 = 1,

        extras: [max_extras]u32 = undefined,
        extra_count: u32 = 0,

        pub fn getOrAddId(pool: *Pool, val: Constant) Id {
            var slot = &pool.buckets[val.hash() % max_buckets];
            while (slot.* != .none) : (slot = &pool.next[@backingInt(slot.*)]) {
                const val1 = pool.unpack(pool.constants[@backingInt(slot.*)]);
                if (val1.eql(val)) break;
            }

            if (slot.* == .none) {
                slot.* = @fromBackingInt(pool.next_id);
                pool.next_id += 1;
                pool.constants[@backingInt(slot.*)] = pool.pack(val);
            }
            return slot.*;
        }

        pub fn get(pool: *Pool, id: Id) Constant {
            debug.assert(id != .none, "constant pool get id");
            return pool.unpack(pool.constants[@backingInt(id)]);
        }

        const Packed = struct {
            tag: Tag,
            v: u32,
        };

        fn pack(pool: *Pool, val: Constant) Packed {
            return switch (val.tag) {
                .type_lit => .{ .tag = val.tag, .v = @backingInt(val.data.type_lit) },
                .fn_type => blk: {
                    const extra_offset = pool.extra_count;
                    pool.extras[pool.extra_count] = @backingInt(val.data.fn_type.ret);
                    pool.extra_count += 1;

                    pool.extras[pool.extra_count] = @intCast(val.data.fn_type.args.len);
                    pool.extra_count += 1;

                    for (val.data.fn_type.args) |arg| {
                        pool.extras[pool.extra_count] = @backingInt(arg);
                        pool.extra_count += 1;
                    }

                    break :blk .{ .tag = val.tag, .v = extra_offset };
                },
            };
        }

        fn unpack(pool: *Pool, p: Packed) Constant {
            return switch (p.tag) {
                .type_lit => .{
                    .tag = p.tag,
                    .data = .{ .type_lit = @fromBackingInt(p.v) },
                },
                .fn_type => blk: {
                    const ret: Id = @fromBackingInt(pool.extras[p.v]);
                    const count = pool.extras[p.v + 1];
                    const ptr: [*]Id = @ptrCast(&pool.extras[p.v + 2]);
                    break :blk .{
                        .tag = p.tag,
                        .data = .{ .fn_type = .{
                            .ret = ret,
                            .args = ptr[0..count],
                        } },
                    };
                },
            };
        }
    };
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
