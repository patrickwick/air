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

fn checkFunction(allocator: std.mem.Allocator, writer: anytype, tokenizer: anytype, function_name: []const u8) !void {
    std.log.info("Checking function: '{s}'", .{function_name});

    var context = Context(@TypeOf(tokenizer.*)).init(allocator, writer.any(), tokenizer);
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

                const ref = try air.reference(tokenizer);
                if (tokenizer.nextToken() != Token.equal) return error.unexpectedToken;
                if (!ref.is_unreferenced) try context.addSymbol(ref.id);

                const instruction_token = tokenizer.nextToken();
                std.log.debug("AIR instruction: {}", .{instruction_token});

                if (tokenizer.nextToken() != Token.bracketOpen) return error.unexpectedToken;
                try air.expression(&context, ref, instruction_token);
                if (tokenizer.nextToken() != Token.bracketClose) return error.unexpectedToken;
            },
            else => _ = tokenizer.nextToken(),
        }
    }

    try context.renderConstraints();
    try context.model.checkResult();
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

    var tokenizer = Tokenizer.IncrementalTokenizer{ .code = air_content };
    defer tokenizer.deinit();

    var token = tokenizer.nextToken();
    while (token != Token.endOfFile) : (token = tokenizer.nextToken()) {
        switch (token) {
            .hash => {
                const name_optional = air.functionName(&tokenizer);
                if (name_optional) |name| {
                    if (std.mem.eql(u8, name, "main")) {
                        // if (std.mem.eql(u8, name, "divide")) {
                        try checkFunction(allocator, &writer, &tokenizer, name);
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
