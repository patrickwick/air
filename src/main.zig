const std = @import("std");

const Tokenizer = @import("Tokenizer.zig");
const Token = Tokenizer.Token;
const air = @import("air.zig");
const Model = @import("Model.zig");

fn Context(TokenizerType: type) type {
    return struct {
        model: Model,
        writer: std.io.AnyWriter,
        tokenizer: *TokenizerType,

        pub fn init(allocator: std.mem.Allocator, writer: std.io.AnyWriter, tokenizer: *TokenizerType) @This() {
            return .{
                .model = Model.init(allocator),
                .writer = writer,
                .tokenizer = tokenizer,
            };
        }

        pub fn deinit(self: *@This()) void {
            self.model.deinit();
        }

        pub fn addError(self: *@This(), location: std.builtin.SourceLocation, error_code: anyerror) anyerror {
            const source_location = self.tokenizer.getCurrentSourceLocation();

            // TODO: store error context and print them at the end. Some errors are not fatal.
            // const ParserErrorContext = struct {
            //     error_code: anyerror, // TODO: add error type
            //     location: Tokenizer.TokenizerSourceLocation,
            //     expected: Token,
            //     actual: Token,
            //     stack_frame_addresses: [20]usize, // TODO: add type - arbitrary max frame count
            // };

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

        pub fn addSymbol(self: *@This(), id: air.RefereceId) !void {
            try self.writer.print(
                \\x{d} = z3.Int('x{d}')
                \\
            , .{ id, id });

            try self.model.addSymbol(id);
        }

        pub fn addSymbolString(self: *@This(), identifier: []const u8) !void {
            // TODO: supports integers only
            try self.writer.print(
                \\{s} = z3.Int('{s}')
                \\
            , .{ identifier, identifier });

            try self.model.addSymbolString(identifier);
        }

        pub fn addEquivalence(self: *@This(), left: air.Reference, right: air.Argument) !void {
            switch (right) {
                .reference => |ref| {
                    try self.writer.print(
                        \\x{d} = x{d}
                        \\
                    , .{ left.id, ref.id });
                },
                .literal => |literal| {
                    if (std.mem.eql(u8, literal, "undefined")) {
                        try self.writer.print(
                            \\# x{d} is undefined
                            \\
                        , .{left.id});
                    } else {
                        try self.writer.print(
                            \\x{d} = {s}
                            \\
                        , .{ left.id, literal });
                    }
                },
                .type_identifier => return self.addError(@src(), error.unexpectedType),
            }

            try self.model.addEquivalence(left, right);
        }

        pub fn addOperation(self: *@This(), left: air.Reference, first: air.Argument, second: air.Argument, operator: Model.Operator) !void {
            const op = switch (operator) {
                .plus => "+",
                .minus => "-",
                .multiply => "*",
                .divide => "/",
            };

            switch (first) {
                .reference => |first_ref| {
                    switch (second) {
                        .reference => |second_ref| {
                            try self.writer.print("x{d} = x{d} {s} x{d}", .{ left.id, first_ref.id, op, second_ref.id });
                        },
                        .literal => |second_literal| {
                            try self.writer.print("x{d} = x{d} {s} {s}", .{ left.id, first_ref.id, op, second_literal });
                        },
                        .type_identifier => return self.addError(@src(), error.unexpectedType),
                    }
                },
                .literal => |first_literal| {
                    switch (second) {
                        .reference => |second_ref| {
                            try self.writer.print("x{d} = {s} {s} x{d}", .{ left.id, first_literal, op, second_ref.id });
                        },
                        .literal => |second_literal| {
                            try self.writer.print("x{d} = {s} {s} x{d}", .{ left.id, first_literal, op, second_literal });
                        },
                        .type_identifier => return self.addError(@src(), error.unexpectedType),
                    }
                },
                .type_identifier => return self.addError(@src(), error.unexpectedType),
            }
            try self.writer.writeByte('\n');

            try self.model.addOperation(left, first, second, operator);
        }

        pub fn addConstraint(self: *@This(), left: air.Argument, right: air.Argument, comparison: Model.Comparison, is_or: bool) !void {
            try self.model.addConstraint(left, right, comparison, is_or);
        }

        pub fn renderConstraints(self: *@This()) !void {
            const Py = struct {
                fn renderConstraint(context: anytype, constraint: *const Model.Constraint) !void {
                    // FIXME: support left hand side literal
                    if (constraint.left != .reference) return error.unexpectedType;

                    const left = constraint.left.reference;
                    const right = constraint.right;

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
                            try context.writer.print(
                                \\x{d} {s} x{d}
                            , .{ left.id, comp, ref.id });
                        },
                        .literal => |literal| {
                            if (std.mem.eql(u8, literal, "undefined")) return context.addError(@src(), error.unexpectedType);

                            try context.writer.print(
                                \\x{d} {s} {s}
                            , .{ left.id, comp, literal });
                        },
                        .type_identifier => return context.addError(@src(), error.unexpectedType),
                    }
                }
            };

            // TODO: leaky abstraction: Or before And because of py, not required for z3
            try self.writer.writeAll("# constraints\n");
            try self.writer.writeAll("s.add(z3.Or(");
            for (self.model.constraints.items) |constraint| {
                if (!constraint.is_or) continue;
                try Py.renderConstraint(self, &constraint);
                try self.model.renderConstraint(&constraint);
                try self.writer.writeAll(", "); // python allows trailing comma
            }
            try self.writer.writeAll("))\n");

            try self.writer.writeAll("s.add(z3.And(");
            for (self.model.constraints.items) |constraint| {
                if (constraint.is_or) continue;
                try Py.renderConstraint(self, &constraint);
                try self.model.renderConstraint(&constraint);
                try self.writer.writeAll(", "); // python allows trailing comma
            }
            try self.writer.writeAll("))\n");
        }
    };
}

// TODO: mutating the model inside context is bad design => should return model detached from context
fn createModel(context: anytype, tokenizer: anytype) !void {
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

                const ref = try air.reference(tokenizer);
                if (tokenizer.nextToken() != Token.equal) return error.unexpectedToken;
                if (!ref.is_unreferenced) try context.addSymbol(ref.id);

                const instruction_token = tokenizer.nextToken();
                std.log.debug("AIR instruction: {}", .{instruction_token});

                if (tokenizer.nextToken() != Token.bracketOpen) return error.unexpectedToken;
                try air.expression(context, ref, instruction_token);
                if (tokenizer.nextToken() != Token.bracketClose) return error.unexpectedToken;
            },
            else => _ = tokenizer.nextToken(),
        }
    }

    try context.renderConstraints();
}

fn checkFunction(allocator: std.mem.Allocator, writer: anytype, tokenizer: anytype) !void {
    var context = Context(@TypeOf(tokenizer.*)).init(allocator, writer.any(), tokenizer);
    defer context.deinit();

    try createModel(&context, context.tokenizer);
    _ = try context.model.checkResult(); // TODO: print findings
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

    const air_content = std.fs.cwd().readFileAlloc(allocator, "build/air", std.math.maxInt(usize)) catch |err| {
        std.log.err("Failed reading AIR", .{});
        return err;
    };
    defer allocator.free(air_content);

    var tokenizer = Tokenizer.IncrementalTokenizer{ .source = air_content };
    defer tokenizer.deinit();

    var token = tokenizer.nextToken();
    while (token != Token.endOfFile) : (token = tokenizer.nextToken()) {
        switch (token) {
            .hash => {
                const name_optional = air.functionName(&tokenizer);
                if (name_optional) |name| {
                    if (std.mem.eql(u8, name, "main")) {
                        // if (std.mem.eql(u8, name, "divide")) {
                        try checkFunction(allocator, &writer, &tokenizer);
                        break;
                    }
                }
            },
            else => {},
        }
    }
}

const t = std.testing;

// TODO: add test set folder with more cases
test "Zero division" {
    // TODO: simplify the division by zero test
    const air_content =
        \\# Begin Function AIR: zero_division.main:
        \\# Total AIR+Liveness bytes: 1.6015625KiB
        \\# AIR Instructions:         72 (648B)
        \\# AIR Extra Data:           145 (580B)
        \\# Liveness tomb_bits:       40B
        \\# Liveness Extra Data:      37 (148B)
        \\# Liveness special table:   15 (120B)
        \\  %0!= dbg_stmt(2:5)
        \\  %1 = alloc(*usize)
        \\  %2!= store_safe(%1, <usize, undefined>)
        \\  %3!= dbg_var_ptr(%1, "c")
        \\  %4!= dbg_stmt(3:5)
        \\  %5 = load(usize, %1)
        \\  %6!= dbg_stmt(3:7)
        \\  %7 = mul_with_overflow(struct{usize, u1}, %5!, <usize, 2>)
        \\  %8 = struct_field_val(%7, 1)
        \\  %9 = cmp_eq(%8!, <u1, 0>)
        \\  %12!= block(void, {
        \\    %13!= cond_br(%9!, likely {
        \\      %14!= br(%12, @Air.Inst.Ref.void_value)
        \\    }, cold {
        \\      %1! %7!
        \\      %10!= call(<fn ([]const u8, ?*const builtin.StackTrace, ?usize) noreturn, (function 'defaultPanic')>, [<[]const u8, "integer overflow"[0..16]>, <?*const builtin.StackTrace, null>, <?usize, null>])
        \\      %11!= unreach()
        \\    })
        \\  } %9!)u
        \\  %15 = struct_field_val(%7!, 0)
        \\  %16!= store_safe(%1, %15!)
        \\  %17!= dbg_stmt(5:5)
        \\  %18 = alloc(*usize)
        \\  %19!= store_safe(%18, <usize, 20>)
        \\  %20!= dbg_var_ptr(%18, "e")
        \\  %21!= dbg_stmt(6:5)
        \\  %22 = load(usize, %18)
        \\  %23!= dbg_stmt(6:7)
        \\  %24 = mul_with_overflow(struct{usize, u1}, %22!, <usize, 5>)
        \\  %25 = struct_field_val(%24, 1)
        \\  %26 = cmp_eq(%25!, <u1, 0>)
        \\  %29!= block(void, {
        \\    %30!= cond_br(%26!, likely {
        \\      %31!= br(%29, @Air.Inst.Ref.void_value)
        \\    }, cold {
        \\      %1! %24! %18!
        \\      %27!= call(<fn ([]const u8, ?*const builtin.StackTrace, ?usize) noreturn, (function 'defaultPanic')>, [<[]const u8, "integer overflow"[0..16]>, <?*const builtin.StackTrace, null>, <?usize, null>])
        \\      %28!= unreach()
        \\    })
        \\  } %26!)
        \\  %32 = struct_field_val(%24!, 0)
        \\  %33!= store_safe(%18, %32!)
        \\  %34!= dbg_stmt(8:5)
        \\  %35 = load(usize, %1)
        \\  %36 = load(usize, %18)
        \\  %37!= dbg_stmt(8:27)
        \\  %38 = sub_with_overflow(struct{usize, u1}, %35!, %36!)
        \\  %39 = struct_field_val(%38, 1)
        \\  %40 = cmp_eq(%39!, <u1, 0>)
        \\  %43!= block(void, {
        \\    %44!= cond_br(%40!, likely {
        \\      %45!= br(%43, @Air.Inst.Ref.void_value)
        \\    }, cold {
        \\      %1! %38! %18!
        \\      %41!= call(<fn ([]const u8, ?*const builtin.StackTrace, ?usize) noreturn, (function 'defaultPanic')>, [<[]const u8, "integer overflow"[0..16]>, <?*const builtin.StackTrace, null>, <?usize, null>])
        \\      %42!= unreach()
        \\    })
        \\  } %40!)
        \\  %46 = struct_field_val(%38!, 0)
        \\  %47!= dbg_stmt(8:22)
        \\  %48 = cmp_neq(%46, @Air.Inst.Ref.zero_usize)
        \\  %51!= block(void, {
        \\    %52!= cond_br(%48!, likely {
        \\      %53!= br(%51, @Air.Inst.Ref.void_value)
        \\    }, cold {
        \\      %1! %46! %18!
        \\      %49!= call(<fn ([]const u8, ?*const builtin.StackTrace, ?usize) noreturn, (function 'defaultPanic')>, [<[]const u8, "division by zero"[0..16]>, <?*const builtin.StackTrace, null>, <?usize, null>])
        \\      %50!= unreach()
        \\    })
        \\  } %48!)
        \\  %54 = div_trunc(<usize, 2>, %46!)
        \\  %55!= dbg_var_val(%54!, "result")
        \\  %56!= dbg_stmt(10:15)
        \\  %57 = load(usize, %1!)
        \\  %58 = load(usize, %18!)
        \\  %59!= dbg_stmt(10:21)
        \\  %60 = sub_with_overflow(struct{usize, u1}, %57!, %58!)
        \\  %61 = struct_field_val(%60, 1)
        \\  %62 = cmp_eq(%61!, <u1, 0>)
        \\  %65!= block(void, {
        \\    %66!= cond_br(%62!, likely {
        \\      %67!= br(%65, @Air.Inst.Ref.void_value)
        \\    }, cold {
        \\      %60!
        \\      %63!= call(<fn ([]const u8, ?*const builtin.StackTrace, ?usize) noreturn, (function 'defaultPanic')>, [<[]const u8, "integer overflow"[0..16]>, <?*const builtin.StackTrace, null>, <?usize, null>])
        \\      %64!= unreach()
        \\    })
        \\  } %62!)
        \\  %68 = struct_field_val(%60!, 0)
        \\  %69!= dbg_stmt(10:15)
        \\  %70!= call(<fn (usize, usize) usize, (function 'divide')>, [<usize, 2>, %68!])
        \\  %71!= ret_safe(<@typeInfo(@typeInfo(@TypeOf(zero_division.main)).@"fn".return_type.?).error_union.error_set!void, {}>)
        \\# End Function AIR: zero_division.main
        \\
    ;

    var tokenizer = Tokenizer.IncrementalTokenizer{ .source = air_content[0..] };
    defer tokenizer.deinit();

    var token = tokenizer.nextToken();
    while (token != Token.endOfFile) : (token = tokenizer.nextToken()) {
        switch (token) {
            .hash => {
                const name_optional = air.functionName(&tokenizer);
                if (name_optional) |name| {
                    if (std.mem.eql(u8, name, "main")) {
                        break;
                    }
                }
            },
            else => {},
        }
    }

    const allocator = t.allocator;
    const writer = std.io.null_writer;

    var context = Context(@TypeOf(tokenizer)).init(allocator, writer.any(), &tokenizer);
    defer context.deinit();

    try createModel(&context, context.tokenizer);
    const model: *Model = &context.model;
    try t.expect(try model.checkResult());

    // TODO: assert that model finds the correct c=50 that would lead to division by zero
}

test {
    std.testing.refAllDecls(@This());
}
