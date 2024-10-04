const std = @import("std");

const Tokenizer = @import("Tokenizer.zig");
const Token = Tokenizer.Token;

const z3 = @import("z3.zig");

fn functionName(tokenizer: anytype) ?[]const u8 {
    // skip "Begin Function AIR:" -> id, id, id, colon
    {
        const begin_token = tokenizer.nextToken();
        if (begin_token != Token.identifier or !std.mem.eql(u8, begin_token.identifier, "Begin")) return null;
    }

    {
        const function_token = tokenizer.nextToken();
        if (function_token != Token.identifier or !std.mem.eql(u8, function_token.identifier, "Function")) return null;
    }

    {
        const air_token = tokenizer.nextToken();
        if (air_token != Token.identifier or !std.mem.eql(u8, air_token.identifier, "AIR")) return null;
    }

    if (tokenizer.nextToken() != Token.colon) return null;

    // TODO: uses only the last part of the symbol -> concatenate
    var name: ?[]const u8 = null;
    var token = tokenizer.nextToken();
    while (token != Token.colon and token != Token.endOfFile) : (token = tokenizer.nextToken()) {
        if (token == Token.identifier) name = token.identifier;
    }
    return name;
}

const RefereceId = u32;

const Reference = struct {
    is_unreferenced: bool,
    id: RefereceId,
};

const Argument = union(enum) {
    reference: Reference,
    literal: Tokenizer.tokens.StringView,
    type_identifier: Tokenizer.tokens.StringView,
};

fn argument(tokenizer: anytype) !Argument {
    switch (tokenizer.lookaheadToken()) {
        // reference, e.g.: "%5!"
        Token.percent => return Argument{ .reference = try reference(tokenizer) },
        // literal, e.g.: "<usize, 2>", "<*[][*:0]u8, os.argv>"
        Token.less => {
            if (tokenizer.nextToken() != Token.less) return error.unexpectedToken;
            if (tokenizer.nextToken() != Token.identifier) return error.unexpectedToken;
            if (tokenizer.nextToken() != Token.comma) return error.unexpectedToken;

            const literal = tokenizer.nextToken();
            if (literal != Token.identifier) return error.unexpectedToken;
            if (tokenizer.nextToken() != Token.greater) return error.unexpectedToken;

            return Argument{ .literal = literal.identifier };
        },
        // string literal, e.g.: dbg_var_ptr(%13, "e")
        Token.quote => {
            if (tokenizer.nextToken() != Token.quote) return error.unexpectedToken;
            const literal = tokenizer.nextToken();
            if (literal != Token.identifier) return error.unexpectedToken;
            if (tokenizer.nextToken() != Token.quote) return error.unexpectedToken;
            return Argument{ .literal = literal.identifier };
        },
        // type, e.g.: "usize", "[][*:0]u8", "struct{usize, u1}"
        else => {
            // TODO: NYI
            try skipType(tokenizer);
            return Argument{ .type_identifier = "TODO: NYI" };
        },
    }
}

fn reference(tokenizer: anytype) !Reference {
    const percent_token = tokenizer.nextToken();
    if (percent_token != Token.percent) return error.unexpectedToken;

    const id_token = tokenizer.nextToken();
    if (id_token != Token.identifier) return error.unexpectedToken;

    const is_unreferenced = tokenizer.lookaheadToken() == Token.exclamation;
    if (is_unreferenced) _ = tokenizer.nextToken(); // remove !

    const id = try std.fmt.parseInt(RefereceId, id_token.identifier, 10);
    return Reference{ .id = id, .is_unreferenced = is_unreferenced };
}

// %38 = sub_with_overflow(struct{usize, u1}, %35!, %36!)
fn skipType(tokenizer: anytype) !void {
    if (tokenizer.lookaheadToken() == Token.struct_type) {
        _ = tokenizer.nextToken();
        while (tokenizer.nextToken() != Token.curlyClose) {}
    }

    while (tokenizer.lookaheadToken() != Token.comma) _ = tokenizer.nextToken();
}

// const ParserErrorContext = struct {
//     error_code: anyerror, // TODO: add error type
//     location: Tokenizer.TokenizerSourceLocation,
//     expected: Token,
//     actual: Token,
//     stack_frame_addresses: [20]usize, // TODO: add type - arbitrary max frame count
// };

// TODO: store error context and print them at the end. Some errors are not fatal.
fn addError(context: anytype, location: std.builtin.SourceLocation, error_code: anyerror) anyerror {
    const source_location = context.tokenizer.getCurrentSourceLocation();

    std.log.err(
        \\Error while parsing: {any} at {d}:{d} called from {s}:{d}:{d}
        \\Source:
        \\{s}
        \\
        \\Stack trace:
    , .{
        error_code,
        source_location.line,
        source_location.column,
        location.fn_name,
        location.line,
        location.column,
        source_location.code_line,
    });

    const max_frames = 20;
    var addresses: [max_frames]usize = [1]usize{0} ** max_frames;
    var stack_trace = std.builtin.StackTrace{
        .instruction_addresses = &addresses,
        .index = 0,
    };
    std.debug.captureStackTrace(@returnAddress(), &stack_trace);
    std.debug.dumpStackTrace(stack_trace);

    return error_code;
}

const Constraint = struct {
    left: Argument,
    right: Argument,
    comparison: Comparison,
    is_or: bool,
};

// TODO: put writer into context too or remove it
// => anytype everywhere can be removed without a writer or use a function pointer instead
// TODO: same for tokenizer
fn Context(WriterType: type, TokenizerType: type) type {
    return struct {
        // TODO: data structure can be optimized (GPA auto map is very basic)
        const SymbolMap = std.AutoHashMap(RefereceId, z3.Z3_ast);
        const ConstraintArray = std.ArrayList(Constraint);

        z3_context: z3.Z3_context,
        z3_solver: z3.Z3_solver,
        z3_int_sort: z3.Z3_sort,
        writer: *const WriterType,
        tokenizer: *TokenizerType,
        symbol_map: SymbolMap,
        constraints: ConstraintArray,

        fn init(z3_context: z3.Z3_context, z3_solver: z3.Z3_solver, z3_int_sort: z3.Z3_sort, writer: *const WriterType, tokenizer: *TokenizerType, allocator: std.mem.Allocator) @This() {
            return .{
                .z3_context = z3_context,
                .z3_solver = z3_solver,
                .z3_int_sort = z3_int_sort,
                .writer = writer,
                .tokenizer = tokenizer,
                .symbol_map = SymbolMap.init(allocator),
                .constraints = ConstraintArray.init(allocator),
            };
        }

        fn deinit(self: *@This()) void {
            self.symbol_map.deinit();
            self.constraints.deinit();
        }
    };
}

const Operator = enum {
    plus,
    minus,
    multiply,
    divide,
};

const Comparison = enum {
    equal,
    not_equal,
    greater,
    greater_equal,
    less,
    less_equal,
};

fn addSymbol(context: anytype, id: RefereceId) !void {
    try context.writer.print(
        \\x{d} = z3.Int('x{d}')
        \\
    , .{ id, id });

    const symbol = z3.Z3_mk_int_symbol(context.z3_context, @intCast(id)) orelse @panic("Z3_mk_int_symbol failed");
    const ast = z3.Z3_mk_const(context.z3_context, symbol, context.z3_int_sort) orelse @panic("Z3_mk_const failed");
    try context.symbol_map.put(id, ast);
}

fn addEquivalence(context: anytype, left: Reference, right: Argument) !void {
    const left_ast = context.symbol_map.get(left.id) orelse @panic("symbol not found");

    switch (right) {
        .reference => |ref| {
            // TODO: supports integers only
            try context.writer.print(
                \\x{d} = x{d}
                \\
            , .{ left.id, ref.id });

            const right_ast = context.symbol_map.get(ref.id) orelse @panic("symbol not found");
            // FIXME: connection between symbols and operations is not correct
            // => equality needs to reach the constraint, otherwise it will not propagate
            const eq = z3.Z3_mk_eq(context.z3_context, left_ast, right_ast) orelse @panic("z3.Z3_mk_eq failed");
            z3.Z3_solver_assert(context.z3_context, context.z3_solver, eq);
        },
        .literal => |literal| {
            if (std.mem.eql(u8, literal, "undefined")) {
                // TODO: add analysis that there is no read before the first write
                try context.writer.print(
                    \\# x{d} is undefined
                    \\
                , .{left.id});
            } else {
                // TODO: supports integers only
                try context.writer.print(
                    \\x{d} = {s}
                    \\
                , .{ left.id, literal });

                const value = try std.fmt.parseInt(usize, literal, 10);
                const right_ast = z3.Z3_mk_int64(context.z3_context, @intCast(value), context.z3_int_sort);
                const eq = z3.Z3_mk_eq(context.z3_context, left_ast, right_ast) orelse @panic("z3.Z3_mk_eq failed");
                z3.Z3_solver_assert(context.z3_context, context.z3_solver, eq);
            }
        },
        .type_identifier => return addError(context, @src(), error.unexpectedType),
    }
}

fn z3Operation(context: anytype, left_ast: z3.Z3_ast, first_ast: z3.Z3_ast, second_ast: z3.Z3_ast, operator: Operator) z3.Z3_ast {
    // NOTE: assumes that Z3 copies the arguments instead of keeping a pointer to stack memory
    const argument_count = 2;
    const argument_slice = [_]z3.Z3_ast{ first_ast, second_ast };
    const arguments: [*c]const z3.Z3_ast = @ptrCast(&argument_slice);

    const op = switch (operator) {
        .plus => z3.Z3_mk_add(context.z3_context, argument_count, arguments) orelse @panic("Z3_mk_add"),
        .minus => z3.Z3_mk_sub(context.z3_context, argument_count, arguments) orelse @panic("Z3_mk_sub"),
        .multiply => z3.Z3_mk_mul(context.z3_context, argument_count, arguments) orelse @panic("Z3_mk_mul"),
        .divide => z3.Z3_mk_div(context.z3_context, first_ast, second_ast) orelse @panic("Z3_mk_div"),
    };

    return z3.Z3_mk_eq(context.z3_context, left_ast, op) orelse @panic("z3.Z3_mk_eq failed");
}

fn addOperation(context: anytype, left: Reference, first: Argument, second: Argument, operator: Operator) !void {
    const left_ast = context.symbol_map.get(left.id) orelse @panic("symbol not found");

    const op = switch (operator) {
        .plus => "+",
        .minus => "-",
        .multiply => "*",
        .divide => "/",
    };

    switch (first) {
        .reference => |first_ref| {
            const first_ast = context.symbol_map.get(first_ref.id) orelse @panic("symbol not found");
            switch (second) {
                .reference => |second_ref| {
                    try context.writer.print("x{d} = x{d} {s} x{d}", .{ left.id, first_ref.id, op, second_ref.id });

                    const second_ast = context.symbol_map.get(second_ref.id) orelse @panic("symbol not found");
                    const equality = z3Operation(context, left_ast, first_ast, second_ast, operator);
                    _ = equality;
                },
                .literal => |second_literal| {
                    try context.writer.print("x{d} = x{d} {s} {s}", .{ left.id, first_ref.id, op, second_literal });

                    // FIXME: literal is not necessarily an integer
                    const second_value = std.fmt.parseInt(usize, second_literal, 10) catch {
                        std.log.err("Invalid literal, dropping operation: {s}", .{second_literal});
                        return;
                    };
                    const second_ast = z3.Z3_mk_int64(context.z3_context, @intCast(second_value), context.z3_int_sort);
                    const equality = z3Operation(context, left_ast, first_ast, second_ast, operator);
                    _ = equality;
                },
                .type_identifier => return addError(context, @src(), error.unexpectedType),
            }
        },
        .literal => |first_literal| {
            // FIXME: literal is not necessarily an integer
            const first_value = std.fmt.parseInt(usize, first_literal, 10) catch {
                std.log.err("Invalid literal, dropping operation: {s}", .{first_literal});
                return;
            };
            const first_ast = z3.Z3_mk_int64(context.z3_context, @intCast(first_value), context.z3_int_sort);

            switch (second) {
                .reference => |second_ref| {
                    try context.writer.print("x{d} = {s} {s} x{d}", .{ left.id, first_literal, op, second_ref.id });

                    const second_ast = context.symbol_map.get(second_ref.id) orelse @panic("symbol not found");
                    const equality = z3Operation(context, left_ast, first_ast, second_ast, operator);
                    _ = equality;
                },
                .literal => |second_literal| {
                    try context.writer.print("x{d} = {s} {s} x{d}", .{ left.id, first_literal, op, second_literal });

                    // FIXME: literal is not necessarily an integer
                    const second_value = std.fmt.parseInt(usize, second_literal, 10) catch {
                        std.log.err("Invalid literal, dropping operation: {s}", .{second_literal});
                        return;
                    };
                    const second_ast = z3.Z3_mk_int64(context.z3_context, @intCast(second_value), context.z3_int_sort);
                    const equality = z3Operation(context, left_ast, first_ast, second_ast, operator);
                    _ = equality;
                },
                .type_identifier => return addError(context, @src(), error.unexpectedType),
            }
        },
        .type_identifier => return addError(context, @src(), error.unexpectedType),
    }
    try context.writer.writeByte('\n');
}

fn addConstraint(context: anytype, left: Argument, right: Argument, comparison: Comparison, is_or: bool) !void {
    try context.constraints.append(Constraint{ .left = left, .right = right, .comparison = comparison, .is_or = is_or });
}

fn renderConstraint(context: anytype, constraint: *const Constraint) !void {
    // FIXME: support left hand side literal
    if (constraint.left != .reference) return addError(context, @src(), error.unexpectedType);

    const left = constraint.left.reference;
    const right = constraint.right;
    const left_ast = context.symbol_map.get(left.id) orelse @panic("symbol not found");

    const comp = switch (constraint.comparison) {
        .equal => "==",
        .not_equal => "!=",
        .greater => ">",
        .greater_equal => ">=",
        .less => "<",
        .less_equal => "<=",
    };

    // FIXME: support other comparisons
    if (constraint.comparison != .equal) std.log.warn("Z3 comparison not integrated yet", .{});

    switch (right) {
        .reference => |ref| {
            // TODO: supports integers only
            try context.writer.print(
                \\x{d} {s} x{d}
            , .{ left.id, comp, ref.id });

            const right_ast = context.symbol_map.get(left.id) orelse @panic("symbol not found");
            const eq = z3.Z3_mk_eq(context.z3_context, left_ast, right_ast) orelse @panic("z3.Z3_mk_eq failed");
            z3.Z3_solver_assert(context.z3_context, context.z3_solver, eq);
        },
        .literal => |literal| {
            if (std.mem.eql(u8, literal, "undefined")) return addError(context, @src(), error.unexpectedType);

            // TODO: supports integers only
            try context.writer.print(
                \\x{d} {s} {s}
            , .{ left.id, comp, literal });

            // FIXME: literal is not necessarily an integer
            // These are only added for debugging reason, so it's easier to know the original variable
            const value = std.fmt.parseInt(usize, literal, 10) catch {
                std.log.err("Unsupported literal, dropping constraint: {s} = x{d}", .{ literal, left.id });
                return;
            };
            const right_ast = z3.Z3_mk_int64(context.z3_context, @intCast(value), context.z3_int_sort);
            const eq = z3.Z3_mk_eq(context.z3_context, left_ast, right_ast) orelse @panic("z3.Z3_mk_eq failed");
            z3.Z3_solver_assert(context.z3_context, context.z3_solver, eq);
        },
        .type_identifier => return addError(context, @src(), error.unexpectedType),
    }
}

const FunctionConstraints = struct {
    pub const Input = struct {
        argument_name: []const u8,
        constraint: Constraint,
    };

    // * postconditions if global or internal state is mutated
    // * return address to stack or deleted memory resource
    pub const Output = struct {
        constraint: Constraint,
    };

    inputs: std.ArrayList(Input),
    outputs: std.ArrayList(Output),

    pub fn init(allocator: std.mem.Allocator) @This() {
        return .{
            .inputs = std.ArrayList(Input).init(allocator),
            .outputs = std.ArrayList(Output).init(allocator),
        };
    }
};

fn expression(context: anytype, ref: Reference, instruction_token: Token) !void {
    // TODO: pass context pointer only
    const tokenizer = context.tokenizer;

    // TODO: try, block, etc. are not supported yet
    switch (instruction_token) {
        // %5!= store_safe(%4, <usize, 50>)
        // %11!= store_safe(%4, %10!)
        .store_safe => {
            const store_target = try reference(tokenizer);
            if (tokenizer.nextToken() != Token.comma) return error.unexpectedToken;
            const source = try argument(tokenizer);
            try addEquivalence(context, store_target, source);
        },
        // %13 = load(usize, %4!)
        // %3 = load([][*:0]u8, <*[][*:0]u8, os.argv>)
        .load => {
            // TODO: use data type
            try skipType(tokenizer);
            if (tokenizer.nextToken() != Token.comma) return error.unexpectedToken;

            if (tokenizer.lookaheadToken() == Token.percent) {
                const source = try reference(tokenizer);
                try addEquivalence(context, ref, Argument{ .reference = source });
            } else {
                // TODO: only references are supported, everything else is ignored
                while (tokenizer.lookaheadToken() != Token.bracketClose) _ = tokenizer.nextToken();
            }
        },
        // %0 = arg(usize, "a")
        .arg => {
            const type_name = try argument(tokenizer);
            if (tokenizer.nextToken() != Token.comma) return error.unexpectedToken;
            const argument_name = try argument(tokenizer);

            // TODO: supports integers only
            _ = type_name; // ignored for now
            try context.writer.print(
                \\{s} = z3.Int('{s}')
                \\
            , .{ argument_name.literal, argument_name.literal });

            try addConstraint(context, Argument{ .reference = ref }, argument_name, .equal, false);
        },
        // %15 = sub_safe(%13!, <usize, 100>)
        .sub_safe => {
            const first = try argument(tokenizer);
            if (tokenizer.nextToken() != Token.comma) return error.unexpectedToken;
            const second = try argument(tokenizer);
            try addOperation(context, ref, first, second, .minus);
        },
        .mul_safe => {
            const first = try argument(tokenizer);
            if (tokenizer.nextToken() != Token.comma) return error.unexpectedToken;
            const second = try argument(tokenizer);
            try addOperation(context, ref, first, second, .multiply);
        },
        // %23 = add_with_overflow(struct{usize, u1}, %21!, <usize, 16>)
        .add_with_overflow => {
            try skipType(tokenizer); // TODO: type not supported, usize only
            if (tokenizer.nextToken() != Token.comma) return error.unexpectedToken;

            const first = try argument(tokenizer);
            if (tokenizer.nextToken() != Token.comma) return error.unexpectedToken;
            const second = try argument(tokenizer);

            // TODO: Overflow constraint
            // try context.writer.print("# overflow checked\n", .{});
            // try addConstraint(context, ...)
            try addOperation(context, ref, first, second, .plus);
        },
        // %38 = sub_with_overflow(struct{usize, u1}, %35!, %36!)
        .sub_with_overflow => {
            try skipType(tokenizer); // TODO: type not supported, usize only
            if (tokenizer.nextToken() != Token.comma) return error.unexpectedToken;

            const first = try argument(tokenizer);
            if (tokenizer.nextToken() != Token.comma) return error.unexpectedToken;
            const second = try argument(tokenizer);

            // Underflow constraint
            try context.writer.print("# underflow checked\n", .{});
            try addConstraint(context, first, second, .greater, true);
            try addOperation(context, ref, first, second, .minus);
        },
        // %7 = mul_with_overflow(struct{usize, u1}, %5!, <usize, 2>)
        .mul_with_overflow => {
            try skipType(tokenizer);
            if (tokenizer.nextToken() != Token.comma) return error.unexpectedToken;

            const first = try argument(tokenizer);
            if (tokenizer.nextToken() != Token.comma) return error.unexpectedToken;
            const second = try argument(tokenizer);
            try addOperation(context, ref, first, second, .multiply);
        },
        // %23 = div_trunc(<usize, 123>, %15!)
        // %54 = div_trunc(@Air.Inst.Ref.one_usize, %46!)
        .div_trunc => {
            const first = try argument(tokenizer);
            if (tokenizer.nextToken() != Token.comma) return error.unexpectedToken;
            const second = try reference(tokenizer);
            // Add constraint that there cannot be a division by zero
            try context.writer.print("# division by zero checked\n", .{});
            try addConstraint(context, Argument{ .reference = second }, Argument{ .literal = "0" }, .equal, true);
            try addOperation(context, ref, first, Argument{ .reference = second }, .divide);
        },
        // %32 = struct_field_val(%24!, 0)
        .struct_field_val => {
            const source = try reference(tokenizer);
            if (tokenizer.nextToken() != Token.comma) return error.unexpectedToken;

            // TODO: hardcoded to only select the first field of the struct since the second field is a success bool
            const identifier = tokenizer.nextToken();
            if (identifier != Token.identifier) return error.unexpectedToken;
            if (std.mem.eql(u8, identifier.identifier, "0")) {
                try addEquivalence(context, ref, Argument{ .reference = source });
            }
        },
        // Add an additional constraint with the symbol name for better readibility when outputting the model
        // %15!= dbg_var_ptr(%13, "e")
        .dbg_var_ptr => {
            const store_target = try reference(tokenizer);
            if (tokenizer.nextToken() != Token.comma) return error.unexpectedToken;

            if (tokenizer.nextToken() != Token.quote) return error.unexpectedToken;
            const store_source = tokenizer.nextToken();
            if (store_source != Token.identifier) return error.unexpectedToken;
            if (tokenizer.nextToken() != Token.quote) return error.unexpectedToken;

            // TODO: supports integers only
            try context.writer.print(
                \\{s} = z3.Int('{s}')
                \\
            , .{ store_source.identifier, store_source.identifier });

            // NOTE: constraint, not equivalence, otherwise this will be simplified out
            try context.writer.print("# name alias x{d}={s}\n", .{ store_target.id, store_source.identifier });
            // FIXME: adding constraint for alias does not work as expected
            // try addConstraint(context, Argument{ .reference = store_target }, Argument{ .literal = store_source.identifier }, .equal, false);
        },
        // TODO: add cond_br, cmp_neq, etc. for if and switch statements
        else => {
            std.log.debug("Ignored {}", .{instruction_token});
            var bracket_count: usize = 1;
            while (bracket_count > 0) {
                const lookahead = tokenizer.lookaheadToken();
                switch (lookahead) {
                    .bracketOpen => bracket_count += 1,
                    .bracketClose => bracket_count -= 1,
                    else => {},
                }
                // last closing bracket is not consumed
                if (lookahead != Token.bracketClose or bracket_count > 0) _ = tokenizer.nextToken();
            }
        },
    }
}

fn extractFunction(allocator: std.mem.Allocator, writer: anytype, tokenizer: anytype, function_name: []const u8) !void {
    std.log.info("Extracting function: '{s}'", .{function_name});

    const z3_config = z3.Z3_mk_config();
    defer z3.Z3_del_config(z3_config);
    // z3.Z3_set_param_value(z3_config, param_id: Z3_string, param_value: Z3_string)

    const z3_context = z3.Z3_mk_context(z3_config);
    defer z3.Z3_del_context(z3_context);

    const z3_solver = z3.Z3_mk_solver(z3_context);
    defer z3.Z3_solver_dec_ref(z3_context, z3_solver);

    const z3_int_sort = z3.Z3_mk_int_sort(z3_context);

    var context = Context(
        @TypeOf(writer.*),
        @TypeOf(tokenizer.*),
    ).init(
        z3_context,
        z3_solver,
        z3_int_sort,
        writer,
        tokenizer,
        allocator,
    );
    defer context.deinit();

    // remove other header information
    while (tokenizer.lookaheadToken() != Token.percent and tokenizer.lookaheadToken() != Token.endOfFile) : (_ = tokenizer.nextToken()) {}

    // read tokens until "# End Function Air"
    var token = tokenizer.lookaheadToken();
    while (token != Token.hash and token != Token.endOfFile) : (token = tokenizer.lookaheadToken()) {
        switch (token) {
            .percent => {
                // debug print whole line
                {
                    const location = tokenizer.getCurrentSourceLocation();
                    std.log.debug("\"{s}\" line {d}", .{ location.code_line, location.line });
                }

                const ref = try reference(tokenizer);
                if (tokenizer.nextToken() != Token.equal) return error.unexpectedToken;
                if (!ref.is_unreferenced) try addSymbol(&context, ref.id);

                const instruction_token = tokenizer.nextToken();
                std.log.debug("AIR instruction: {}", .{instruction_token});

                if (tokenizer.nextToken() != Token.bracketOpen) return error.unexpectedToken;
                try expression(&context, ref, instruction_token);
                if (tokenizer.nextToken() != Token.bracketClose) return error.unexpectedToken;
            },
            else => _ = tokenizer.nextToken(),
        }
    }

    // render constraints
    try context.writer.writeAll("# constraints\n");
    try context.writer.writeAll("s.add(z3.Or(");
    for (context.constraints.items) |constraint| {
        if (!constraint.is_or) continue;
        try renderConstraint(&context, &constraint);
        try context.writer.writeAll(", "); // python allows trailing comma
    }
    try context.writer.writeAll("))\n");

    try context.writer.writeAll("s.add(z3.And(");
    for (context.constraints.items) |constraint| {
        if (constraint.is_or) continue;
        try renderConstraint(&context, &constraint);
        try context.writer.writeAll(", "); // python allows trailing comma
    }
    try context.writer.writeAll("))\n");

    const check_result = z3.Z3_solver_check(z3_context, z3_solver);
    switch (check_result) {
        z3.Z3_L_TRUE, // satisfiable
        z3.Z3_L_UNDEF, // maybe satisfiable
        => {
            const model = z3.Z3_solver_get_model(z3_context, z3_solver);
            z3.Z3_model_inc_ref(z3_context, model);
            defer z3.Z3_model_dec_ref(z3_context, model);

            // debug print model
            const model_string = z3.Z3_model_to_string(context.z3_context, model);
            std.log.info(
                \\Model:
                \\{s}
            , .{model_string});

            const const_count = z3.Z3_model_get_num_consts(z3_context, model);
            std.log.info("Model const count: {d}", .{const_count});

            for (0..const_count) |i| {
                const declaration = z3.Z3_model_get_const_decl(context.z3_context, model, @intCast(i)) orelse @panic("Z3_model_get_const_decl failed");

                const num_args = 0;
                const args = null;
                const app = z3.Z3_mk_app(context.z3_context, declaration, num_args, args) orelse @panic("Z3_mk_app failed");

                const model_completion = true;
                var result: z3.Z3_ast = undefined;
                const success = z3.Z3_model_eval(context.z3_context, model, app, model_completion, &result);
                if (!success) return error.modelcheckingFailed;

                const result_kind = z3.Z3_get_ast_kind(context.z3_context, result);
                const value = switch (result_kind) {
                    z3.Z3_NUMERAL_AST => z3.Z3_get_numeral_string(context.z3_context, result),
                    else => return error.unsupportedType,
                };

                const name = z3.Z3_get_decl_name(context.z3_context, declaration) orelse @panic("Z3_get_decl_name failed");
                const kind = z3.Z3_get_symbol_kind(context.z3_context, name);
                switch (kind) {
                    z3.Z3_INT_SYMBOL => {
                        const id = z3.Z3_get_symbol_int(context.z3_context, name);
                        std.log.info("x{d} = {s}", .{ id, value });
                    },
                    z3.Z3_STRING_SYMBOL => {
                        const id = z3.Z3_get_symbol_string(context.z3_context, name);
                        std.log.info("{s} = {s}", .{ id, value });
                    },
                    else => return error.unsupportedType,
                }
            }
        },
        // not satisfiable
        z3.Z3_L_FALSE => {
            std.log.info("No issues found", .{});
        },
        else => @panic("invalid Z3_solver_check result"),
    }
}

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){}; // TODO: can be optimized
    defer {
        const check = gpa.deinit();
        if (check != .ok) std.log.err("GPA check failed: {}", .{check});
    }
    const allocator = gpa.allocator();

    // NOTE: temporary hack: generating python code before using the actual z3 library
    const out_path = "build/out.py";
    var out_file = try std.fs.cwd().createFile(out_path, std.fs.File.CreateFlags{});
    defer out_file.close();
    const writer = out_file.writer();

    // z3 wrapper code
    try writer.print(
        \\# NOTE: generated code
        \\import z3
        \\s = z3.Solver()
        \\
        \\
    , .{});

    defer {
        writer.print(
            \\
            \\result = s.check()
            \\print('Result:')
            \\print(result)
            \\print()
            \\
            \\print('Statistics:')
            \\print(s.statistics())
            \\print()
            \\
            \\print('Expression:')
            \\print(s.sexpr())
            \\
            \\print('Dimacs')
            \\print(s.dimacs())
            \\
            \\if (result == z3.sat):
            \\    print('Model:')
            \\    print(s.model())
            \\
        , .{}) catch |err| @panic(@errorName(err));
    }

    const air = std.fs.cwd().readFileAlloc(allocator, "build/air", std.math.maxInt(usize)) catch |err| {
        std.log.err("Failed reading AIR", .{});
        return err;
    };
    defer allocator.free(air);

    var tokenizer = Tokenizer.IncrementalTokenizer{ .code = air };
    defer tokenizer.deinit();

    var token = tokenizer.nextToken();
    while (token != Token.endOfFile) : (token = tokenizer.nextToken()) {
        switch (token) {
            .hash => {
                const name_optional = functionName(&tokenizer);
                if (name_optional) |name| {
                    if (std.mem.eql(u8, name, "main")) {
                        // if (std.mem.eql(u8, name, "divide")) {
                        try extractFunction(allocator, &writer, &tokenizer, name);
                        break;
                    }
                }
            },
            else => {},
        }
    }
}

// TODO: inline relevant AIR to test parsing
test {
    std.testing.refAllDecls(@This());
}
