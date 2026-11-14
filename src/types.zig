const stdx = @import("stdx.zig");
const mem = stdx.mem;
const math = stdx.math;
const debug = stdx.debug;

const lexer = @import("lexer.zig");
const analyzer = @import("analyzer.zig");

const typed_lower = @import("lower_typed.zig");

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

        undeclared_identifier,
        exptected_ptr,
        addr_of_comp_type,
        incompatible_peer_types,
        incompatible_cast,
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

    type_pool: Type.Pool,
    constant_pool: Constant.Pool,

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
    value_inst: UntypedIr.InstId,

    tag: enum { variable, constant },
    status: enum { unchecked, checked, check_failed },
};

pub const Ast = struct {
    pub const Tag = enum(u32) {
        file,

        identifier,

        bool_lit,
        undef_lit,
        num_lit,

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
        ret_implicit, // empty

        coerce_type, // lhs - type inst, rhs - value
        type_of,

        global_ptr,
        global_val,

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

    pub const InstId = enum(u32) { none = 0, _ };

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
    inst_count: u32 = 1,

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

pub const Type = union(enum) {
    pub const Id = enum(u32) {
        none = 0,

        comp_undef,
        comp_int,
        comp_float,

        isize,
        usize,

        bool,
        void,
        noreturn,

        type_id,

        _,

        const len = @typeInfo(Id).@"enum".field_names.len;
    };

    pub const Tag = @typeInfo(@This()).@"union".tag_type orelse unreachable;

    const Float = enum(u8) { single, double };

    lit: Id,
    fixed_int: struct { signed: bool, width: u16 },
    float: Float,
    func: struct { ret: Id, args: List },
    ptr: Id,

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

        types: [max_types]Type,
        next_id: u32 = Id.len,

        extras: [max_extras]Id = undefined,
        extra_count: u32 = 0,

        pub fn init(pool: *Pool) void {
            pool.* = .{ .types = undefined };
            for (1..Id.len) |id| {
                pool.types[id] = .{ .lit = @fromBackingInt(@intCast(id)) };
            }
        }

        fn hash(pool: *Pool, t: Type) u64 {
            var fnv = math.Fnv{};
            fnv.roll32(@backingInt(t));
            switch (t) {
                .lit => @panic("lits not hashable"),
                .fixed_int => |i| {
                    if (i.signed) fnv.roll(&.{23}) else fnv.roll(&.{17});
                    fnv.roll(@ptrCast(&i.width));
                },
                .float => |f| fnv.roll(@ptrCast(&f)),
                .ptr => |p| fnv.roll32(@backingInt(p)),
                .func => |f| {
                    fnv.roll32(@backingInt(f.ret));
                    for (0..f.args.count) |i| {
                        fnv.roll32(@backingInt(pool.extras[f.args.offset + i]));
                    }
                },
            }
            return fnv.hash;
        }

        fn eql(pool: *Pool, t1: Type, t2: Type) bool {
            if (@as(Tag, t1) != @as(Tag, t2)) return false;
            return switch (t1) {
                .lit => t1.lit == t2.lit,
                .fixed_int => t1.fixed_int.signed == t2.fixed_int.signed and
                    t1.fixed_int.width == t2.fixed_int.width,
                .float => t1.float == t2.float,
                .ptr => t1.ptr == t2.ptr,
                .func => blk: {
                    if (t1.func.ret != t2.func.ret or
                        t1.func.args.count != t2.func.args.count)
                    {
                        break :blk false;
                    }

                    for (0..t1.func.args.count) |arg_i| {
                        const a1 = pool.extras[t1.func.args.offset + arg_i];
                        const a2 = pool.extras[t2.func.args.offset + arg_i];
                        if (a1 != a2) {
                            break :blk false;
                        }
                    }
                    break :blk true;
                },
            };
        }

        fn getOrCreateId(pool: *Pool, t: Type, extra_marker: u32) Id {
            debug.assert(t != .lit, "cannot create a literal type");
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

        pub fn ptr(pool: *Pool, t: Id) Id {
            return pool.getOrCreateId(.{ .ptr = t }, pool.extra_count);
        }

        pub fn func(pool: *Pool, ret: Id, args: []Id) Id {
            const marker = pool.extra_count;
            const args_list = pool.allocList(args);
            return pool.getOrCreateId(.{ .func = .{
                .args = args_list,
                .ret = ret,
            } }, marker);
        }

        pub fn int(pool: *Pool, signed: bool, width: u16) Id {
            return pool.getOrCreateId(.{ .fixed_int = .{
                .signed = signed,
                .width = width,
            } }, pool.extra_count);
        }

        pub fn float(pool: *Pool, val: Float) Id {
            return pool.getOrCreateId(.{ .float = val }, pool.extra_count);
        }

        pub fn getType(pool: *Pool, id: Id) Type {
            debug.assert(id != .none, "type get none");
            return pool.types[@backingInt(id)];
        }

        pub fn parseLiteral(pool: *Pool, str: []const u8) Type.Id {
            if (mem.eql(str, "bool"))
                return .bool
            else if (mem.eql(str, "void"))
                return .void
            else if (mem.eql(str, "noreturn"))
                return .noreturn
            else if (mem.eql(str, "type_id"))
                return .type_id
            else if (mem.eql(str, "comp_float"))
                return .comp_float
            else if (mem.eql(str, "comp_int"))
                return .comp_int
            else if (mem.eql(str, "usize"))
                return .usize
            else if (mem.eql(str, "isize"))
                return .isize
            else if (mem.eql(str, "f32"))
                return pool.float(.single)
            else if (mem.eql(str, "f64"))
                return pool.float(.double)
            else if (mem.eql(str, "u8"))
                return pool.int(false, 8)
            else if (mem.eql(str, "u16"))
                return pool.int(false, 16)
            else if (mem.eql(str, "u32"))
                return pool.int(false, 32)
            else if (mem.eql(str, "u64"))
                return pool.int(false, 64)
            else if (mem.eql(str, "i8"))
                return pool.int(true, 8)
            else if (mem.eql(str, "i16"))
                return pool.int(true, 16)
            else if (mem.eql(str, "i32"))
                return pool.int(true, 32)
            else if (mem.eql(str, "i64"))
                return pool.int(true, 64)
            else
                return .none;
        }
    };
};

pub const Constant = union(enum) {
    pub const Id = enum(u32) {
        none = 0,

        undef,

        bool_true,
        bool_false,

        _,

        const len = @typeInfo(@This()).@"enum".field_names.len;
    };

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

        constants: [max_constants]Constant,
        next_id: u32 = Id.len,

        pub fn init(pool: *Pool) void {
            pool.* = .{ .constants = undefined };
            pool.constants[@backingInt(Id.undef)] = .undef;
            pool.constants[@backingInt(Id.bool_true)] = .{ .bool = true };
            pool.constants[@backingInt(Id.bool_false)] = .{ .bool = false };
        }

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
        queued: *typed_lower.State,
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
