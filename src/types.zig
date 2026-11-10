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
        expected_operator,
        expected_binding_op,
        expected_expression,
        expected_type,
        expected_lvalue,
        name_shadows_type: TypeLit,
        unexpected_token: struct {
            expected: lexer.Tag,
        },
        duplicate_decl: struct {
            original_pos: Position,
        },
        closure_on_variable: struct {
            original_pos: Position,
        },
    },
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
    func_table: Func.Table = .{},

    type_pool: Type.Pool = .{},
    constant_pool: Constant.Pool = .{},

    analysis_q: analyzer.Queue = .{},

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
    typed_ir: *TypedIr,

    namespace_id: Namespace.Id,
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

    pub const List = struct { offset: u32, count: u32 };

    pub const Node = struct {
        pos: u32,
        tag: Tag,
        data: union {
            block: List,

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
        const result = ast.node_count;
        ast.nodes[result] = node;
        ast.node_count += 1;
        return @fromBackingInt(result);
    }

    pub fn getNode(ast: *Ast, id: NodeId) Node {
        debug.assert(id != .none, "get none ast node");
        debug.assert(id != .poison, "get poison ast node");
        return ast.nodes[@backingInt(id)];
    }

    pub fn allocList(ast: *Ast, ids: []NodeId) List {
        const offset = ast.extra_count;
        for (ids) |id| {
            ast.extras[ast.extra_count] = id;
            ast.extra_count += 1;
        }
        return .{ .offset = offset, .count = @intCast(ids.len) };
    }

    pub const NodeId = enum(u32) { none = 0, poison = 1, _ };

    const max_nodes = 8192;
    const max_extras = 4096;

    nodes: [max_nodes]Node = undefined,
    node_count: u32 = 2,

    extras: [max_extras]NodeId = undefined,
    extra_count: u32 = 0,
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

    pub const List = struct {
        offset: u32,
        count: u32,
    };

    pub const Inst = struct {
        pos: u32,
        tag: Tag,
        data: union {
            empty: void,
            block: List,

            type_lit: TypeLit,
            bool_lit: bool,

            global_ref: InternPool.Id,

            fn_arg: struct { index: u32 },
            fn_lit: struct { type: InstId, body: List },
            fn_type: struct { return_type: InstId, arg_types: List },

            bin_op: struct { lhs: InstId, rhs: InstId },
            unary_op: InstId,
        },
    };

    pub const InstId = enum(u32) { none = 0, poison = 1, _ };

    const max_insts = 8192;
    const max_extras = 8192;

    insts: [max_insts]Inst = undefined,
    inst_count: u32 = 2,

    extras: [max_extras]InstId = undefined,
    extra_count: u32 = 0,

    pub fn getInst(ir: *UntypedIr, id: InstId) Inst {
        debug.assert(id != .none, "get none untyped inst");
        debug.assert(id != .poison, "get poison untyped inst");
        return ir.insts[@backingInt(id)];
    }

    pub fn overwriteInst(ir: *UntypedIr, id: InstId, inst: Inst) void {
        ir.insts[@backingInt(id)] = inst;
    }

    pub fn allocInst(ir: *UntypedIr, inst: Inst) InstId {
        const result = ir.inst_count;
        ir.insts[result] = inst;
        ir.inst_count += 1;
        return @fromBackingInt(result);
    }

    pub fn allocList(ir: *UntypedIr, ids: []InstId) List {
        const offset = ir.extra_count;
        for (ids) |id| {
            ir.extras[ir.extra_count] = id;
            ir.extra_count += 1;
        }
        return .{ .offset = offset, .count = @intCast(ids.len) };
    }
};

pub const TypedIr = struct {
    pub const Tag = enum(u32) {
        constant,

        add,
        subtract,
        mul,
        div,
        mod,

        alloc,
        load,
        store,

        ret,

        func,
    };

    pub const InstId = enum(u32) { none = 0, poison = 1, _ };

    pub const Inst = struct {
        pos: u32,
        tag: Tag,
        type: Type.Id,
        data: union {
            arg: struct { index: u32, type: Type.Id },
            bin_op: struct { lhs: InstId, rhs: InstId },
            unary_op: InstId,
            alloc: Type.Id,
            constant: Constant.Id,
            block: List,
        },
    };

    const max_insts = 8192;
    const max_extras = 4096;

    insts: [max_insts]Inst = undefined,
    inst_count: u32 = 2,

    extras: [max_extras]InstId = undefined,
    extra_count: u32 = 0,

    pub const List = struct {
        offset: u32,
        count: u32,
    };

    pub fn getInst(ir: *TypedIr, id: InstId) Inst {
        debug.assert(id != .none, "get none typed inst");
        return ir.insts[@backingInt(id)];
    }

    pub fn allocInst(ir: *TypedIr, inst: Inst) InstId {
        const result = ir.inst_count;
        ir.insts[result] = inst;
        ir.inst_count += 1;
        return @fromBackingInt(result);
    }

    pub fn allocList(ir: *TypedIr, ids: []InstId) List {
        const offset = ir.extra_count;
        for (ids) |id| {
            ir.extras[ir.extra_count] = id;
            ir.extra_count += 1;
        }
        return .{ .offset = offset, .count = @intCast(ids.len) };
    }
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
    comp_undef,

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

pub const Type = struct {
    pub const Id = enum(u32) { none = 0, _ };

    pub const Tag = enum(u32) {
        lit,
        func,
        ptr,
    };

    tag: Tag,
    data: union {
        lit: TypeLit,
        func: struct { ret: Id, args: List },
        ptr: Id,
    },

    // TODO: this is not good for lookup, even duplicate lookup need to allocate lists
    pub const List = struct {
        offset: u32,
        count: u32,
    };

    pub const Pool = struct {
        const max_types = 4096;
        const max_extras = 2048;
        const max_buckets = 1024;

        buckets: [max_buckets]Id = @splat(.none),
        next: [max_types]Id = @splat(.none),

        types: [max_types]Type = undefined,
        next_id: u32 = 1,

        extras: [max_extras]Id = undefined,
        extra_count: u32 = 0,

        fn hash(pool: *Pool, t: Type) u64 {
            var fnv = math.Fnv{};
            fnv.roll32(@backingInt(t.tag));
            switch (t.tag) {
                .lit => fnv.roll32(@backingInt(t.data.lit)),
                .func => {
                    fnv.roll32(@backingInt(t.data.func.ret));
                    for (0..t.data.func.args.count) |i| {
                        fnv.roll32(@backingInt(pool.extras[t.data.func.args.offset + i]));
                    }
                },
                .ptr => fnv.roll32(@backingInt(t.data.ptr)),
            }
            return fnv.hash;
        }

        fn eql(pool: *Pool, t1: Type, t2: Type) bool {
            if (t1.tag != t2.tag) return false;
            return switch (t1.tag) {
                .lit => t1.data.lit == t2.data.lit,
                .ptr => t1.data.ptr == t2.data.ptr,
                .func => blk: {
                    if (t1.data.func.ret != t2.data.func.ret or
                        t1.data.func.args.count != t2.data.func.args.count)
                    {
                        break :blk false;
                    }

                    for (0..t1.data.func.args.count) |arg_i| {
                        const a1 = pool.extras[t1.data.func.args.offset + arg_i];
                        const a2 = pool.extras[t2.data.func.args.offset + arg_i];
                        if (a1 != a2) {
                            break :blk false;
                        }
                    }

                    break :blk true;
                },
            };
        }

        fn getOrCreateId(pool: *Pool, t: Type, extra_marker: u32) Id {
            var slot = &pool.buckets[pool.hash(t) % max_buckets];
            while (slot.* != .none) : (slot = &pool.next[@backingInt(slot.*)]) {
                if (pool.eql(pool.types[@backingInt(slot.*)], t)) break;
            }

            if (slot.* == .none) {
                slot.* = @fromBackingInt(pool.next_id);
                pool.next_id += 1;
                pool.types[@backingInt(slot.*)] = t;
            } else {
                pool.extra_count = extra_marker;
            }
            return slot.*;
        }

        fn allocList(pool: *Pool, ids: []Id) List {
            const offset = pool.extra_count;
            for (ids) |id| {
                pool.extras[pool.extra_count] = id;
                pool.extra_count += 1;
            }
            return .{
                .offset = offset,
                .count = @intCast(ids.len),
            };
        }

        pub fn literal(pool: *Pool, l: TypeLit) Id {
            return pool.getOrCreateId(.{
                .tag = .lit,
                .data = .{ .lit = l },
            }, pool.extra_count);
        }

        pub fn ptr(pool: *Pool, t: Id) Id {
            return pool.getOrCreateId(.{
                .tag = .ptr,
                .data = .{ .ptr = t },
            }, pool.extra_count);
        }

        pub fn func(pool: *Pool, ret: Id, args: []Id) Id {
            const marker = pool.extra_count;
            const args_list = pool.allocList(args);
            return pool.getOrCreateId(.{
                .tag = .func,
                .data = .{ .func = .{ .args = args_list, .ret = ret } },
            }, marker);
        }

        pub fn getType(pool: *Pool, id: Id) Type {
            debug.assert(id != .none, "type get none");
            return pool.types[@backingInt(id)];
        }
    };
};

pub const Constant = union(enum) {
    pub const Id = enum(u32) { none = 0, _ };

    pub const Tag = enum { int, float, bool, undef };

    undef,
    bool: bool,
    int: i64,
    float: f64,
    global: Symbol.Id,

    fn hash(c: Constant) u64 {
        var fnv = math.Fnv{};
        fnv.roll32(@backingInt(c));
        switch (c) {
            .int => |i| fnv.roll(@ptrCast(&i)),
            .float => |f| fnv.roll(@ptrCast(&f)),
            .bool => |b| fnv.roll(&.{if (b) 5 else 7}),
            .global => |s| fnv.roll32(@backingInt(s)),
            .undef => {},
        }
        return fnv.hash;
    }

    fn eql(c1: Constant, c2: Constant) bool {
        if (@backingInt(c1) != @backingInt(c2)) return false;
        return switch (c1) {
            .int => c1.int == c2.int,
            .float => c1.float == c2.float,
            .bool => c1.bool == c2.bool,
            .undef => true,
            .global => c1.global == c2.global,
        };
    }

    pub const Pool = struct {
        const max_constants = 4096;
        const max_buckets = 1024;

        buckets: [max_buckets]Id = @splat(.none),
        next: [max_constants]Id = @splat(.none),

        constants: [max_constants]Constant = undefined,
        next_id: u32 = 1,

        fn getOrCreateId(pool: *Pool, c: Constant) Id {
            var slot = &pool.buckets[c.hash() % max_buckets];
            while (slot.* != .none) : (slot = &pool.next[@backingInt(slot.*)]) {
                if (pool.constants[@backingInt(slot.*)].eql(c)) break;
            }

            if (slot.* == .none) {
                slot.* = @fromBackingInt(pool.next_id);
                pool.next_id += 1;
                pool.constants[@backingInt(slot.*)] = c;
            }
            return slot.*;
        }

        pub fn undef(pool: *Pool) Id {
            return pool.getOrCreateId(.undef);
        }

        pub fn boolean(pool: *Pool, b: bool) Id {
            return pool.getOrCreateId(.{ .bool = b });
        }

        pub fn int(pool: *Pool, v: i64) Id {
            return pool.getOrCreateId(.{ .int = v });
        }

        pub fn global(pool: *Pool, v: Symbol.Id) Id {
            return pool.getOrCreateId(.{ .global = v });
        }

        pub fn get(pool: *Pool, id: Id) Constant {
            debug.assert(id != .none, "get none constant");
            return pool.constants[@backingInt(id)];
        }
    };
};

pub const Func = struct {
    pub const Id = enum(u32) { none = 0, _ };

    type: Type.Id,
    file: File.Id,
    untyped_inst: UntypedIr.InstId,
    status: union(enum) {
        unchecked,
        queued: *analyzer.Eval,
        checked: TypedIr.InstId,
    },

    pub const Table = struct {
        const max_funcs = 4096;

        funcs: [max_funcs]Func = undefined,
        next_id: u32 = 1,

        pub fn add(table: *Table, func: Func) Id {
            const result = table.next_id;
            table.next_id += 1;
            table.funcs[result] = func;
            return @fromBackingInt(result);
        }

        pub fn get(table: *Table, id: Id) *Func {
            debug.assert(id != .none, "get none func");
            return &table.funcs[@backingInt(id)];
        }
    };
};
