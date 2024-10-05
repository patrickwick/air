const std = @import("std");
const air = @import("air.zig");
const z3 = @import("z3.zig");

const Model = @This();

allocator: std.mem.Allocator,
z3_config: z3.Z3_config,
z3_context: z3.Z3_context,
z3_solver: z3.Z3_solver,
z3_int_sort: z3.Z3_sort,
symbol_map: SymbolMap,
symbol_string_map: SymbolStringMap,
constraints: ConstraintArray,

// TODO: data structure can be optimized (GPA auto map is very basic)
pub const SymbolMap = std.AutoHashMap(air.RefereceId, z3.Z3_ast);
pub const SymbolStringMap = std.StringHashMap(StringSymbol);
pub const ConstraintArray = std.ArrayList(Constraint);

const StringSymbol = struct {
    identifier: [:0]const u8, // heap allocated due to C zero sentinel
    z3_symbol: z3.Z3_ast,
};

pub const Operator = enum {
    plus,
    minus,
    multiply,
    divide,
};

pub const Comparison = enum {
    equal,
    not_equal,
    greater,
    greater_equal,
    less,
    less_equal,
};

pub const Constraint = struct {
    left: air.Argument,
    right: air.Argument,
    comparison: Comparison,
    is_or: bool,
};

pub fn init(allocator: std.mem.Allocator) @This() {
    const z3_config = z3.Z3_mk_config();
    // z3.Z3_set_param_value(z3_config, param_id: Z3_string, param_value: Z3_string)
    const z3_context = z3.Z3_mk_context(z3_config);
    const z3_solver = z3.Z3_mk_solver(z3_context);
    const z3_int_sort = z3.Z3_mk_int_sort(z3_context);

    return .{
        .allocator = allocator,
        .z3_config = z3_config,
        .z3_context = z3_context,
        .z3_solver = z3_solver,
        .z3_int_sort = z3_int_sort,
        .symbol_map = SymbolMap.init(allocator),
        .symbol_string_map = SymbolStringMap.init(allocator),
        .constraints = ConstraintArray.init(allocator),
    };
}

pub fn deinit(self: *@This()) void {
    // deinit in reverse order
    defer z3.Z3_del_config(self.z3_config);
    defer z3.Z3_del_context(self.z3_context);
    defer z3.Z3_solver_dec_ref(self.z3_context, self.z3_solver);
    defer self.symbol_map.deinit();
    defer {
        var it = self.symbol_string_map.iterator();
        while (it.next()) |symbol| {
            self.allocator.free(symbol.value_ptr.identifier);
        }
        self.symbol_string_map.deinit();
    }
    defer self.constraints.deinit();
}

pub fn addSymbol(self: *@This(), id: air.RefereceId) !void {
    const symbol = z3.Z3_mk_int_symbol(self.z3_context, @intCast(id)) orelse @panic("Z3_mk_int_symbol failed");
    const ast = z3.Z3_mk_const(self.z3_context, symbol, self.z3_int_sort) orelse @panic("Z3_mk_const failed");
    try self.symbol_map.put(id, ast);
}

pub fn addSymbolString(self: *@This(), identifier: []const u8) !void {
    const identifier_c = try self.allocator.allocSentinel(u8, identifier.len, 0); // deallocated in deinit
    const symbol = z3.Z3_mk_string_symbol(self.z3_context, identifier_c) orelse @panic("Z3_mk_string_symbol failed");
    const ast = z3.Z3_mk_const(self.z3_context, symbol, self.z3_int_sort) orelse @panic("Z3_mk_const failed");
    try self.symbol_string_map.put(identifier, .{ .identifier = identifier_c, .z3_symbol = ast });
}

pub fn addEquivalence(self: *@This(), left: air.Reference, right: air.Argument) !void {
    const left_ast = self.symbol_map.get(left.id) orelse @panic("symbol not found");

    switch (right) {
        .reference => |ref| {
            const right_ast = self.symbol_map.get(ref.id) orelse @panic("symbol not found");
            // FIXME: connection between symbols and operations is not correct
            // => equality needs to reach the constraint, otherwise it will not propagate
            const eq = z3.Z3_mk_eq(self.z3_context, left_ast, right_ast) orelse @panic("z3.Z3_mk_eq failed");
            z3.Z3_solver_assert(self.z3_context, self.z3_solver, eq);
        },
        .literal => |literal| {
            if (!std.mem.eql(u8, literal, "undefined")) {
                const value = try std.fmt.parseInt(usize, literal, 10);
                const right_ast = z3.Z3_mk_int64(self.z3_context, @intCast(value), self.z3_int_sort);
                const eq = z3.Z3_mk_eq(self.z3_context, left_ast, right_ast) orelse @panic("z3.Z3_mk_eq failed");
                z3.Z3_solver_assert(self.z3_context, self.z3_solver, eq);
            }
        },
        .type_identifier => return error.unexpectedType,
    }
}

pub fn addOperation(self: *@This(), left: air.Reference, first: air.Argument, second: air.Argument, operator: Operator) !void {
    const left_ast = self.symbol_map.get(left.id) orelse @panic("symbol not found");

    switch (first) {
        .reference => |first_ref| {
            const first_ast = self.symbol_map.get(first_ref.id) orelse @panic("symbol not found");
            switch (second) {
                .reference => |second_ref| {
                    const second_ast = self.symbol_map.get(second_ref.id) orelse @panic("symbol not found");
                    const equality = z3Operation(self, left_ast, first_ast, second_ast, operator);
                    _ = equality;
                },
                .literal => |second_literal| {
                    // FIXME: literal is not necessarily an integer
                    const second_value = std.fmt.parseInt(usize, second_literal, 10) catch {
                        std.log.err("Invalid literal, dropping operation: {s}", .{second_literal});
                        return;
                    };
                    const second_ast = z3.Z3_mk_int64(self.z3_context, @intCast(second_value), self.z3_int_sort);
                    const equality = z3Operation(self, left_ast, first_ast, second_ast, operator);
                    _ = equality;
                },
                .type_identifier => return error.unexpectedType,
            }
        },
        .literal => |first_literal| {
            // FIXME: literal is not necessarily an integer
            const first_value = std.fmt.parseInt(usize, first_literal, 10) catch {
                std.log.err("Invalid literal, dropping operation: {s}", .{first_literal});
                return;
            };
            const first_ast = z3.Z3_mk_int64(self.z3_context, @intCast(first_value), self.z3_int_sort);

            switch (second) {
                .reference => |second_ref| {
                    const second_ast = self.symbol_map.get(second_ref.id) orelse @panic("symbol not found");
                    const equality = z3Operation(self, left_ast, first_ast, second_ast, operator);
                    _ = equality;
                },
                .literal => |second_literal| {
                    // FIXME: literal is not necessarily an integer
                    const second_value = std.fmt.parseInt(usize, second_literal, 10) catch {
                        std.log.err("Invalid literal, dropping operation: {s}", .{second_literal});
                        return;
                    };
                    const second_ast = z3.Z3_mk_int64(self.z3_context, @intCast(second_value), self.z3_int_sort);
                    const equality = z3Operation(self, left_ast, first_ast, second_ast, operator);
                    _ = equality;
                },
                .type_identifier => return error.unexpectedType,
            }
        },
        .type_identifier => return error.unexpectedType,
    }
}

pub fn addConstraint(self: *@This(), left: air.Argument, right: air.Argument, comparison: Comparison, is_or: bool) !void {
    try self.constraints.append(Constraint{ .left = left, .right = right, .comparison = comparison, .is_or = is_or });
}

pub fn checkResult(self: *@This()) !bool {
    const check_result = z3.Z3_solver_check(self.z3_context, self.z3_solver);
    switch (check_result) {
        z3.Z3_L_TRUE, // satisfiable
        z3.Z3_L_UNDEF, // maybe satisfiable
        => {
            const model = z3.Z3_solver_get_model(self.z3_context, self.z3_solver);
            z3.Z3_model_inc_ref(self.z3_context, model);
            defer z3.Z3_model_dec_ref(self.z3_context, model);

            // debug print model
            const model_string = z3.Z3_model_to_string(self.z3_context, model);
            std.log.info(
                \\Model:
                \\{s}
            , .{model_string});

            const const_count = z3.Z3_model_get_num_consts(self.z3_context, model);
            std.log.info("Model const count: {d}", .{const_count});

            for (0..const_count) |i| {
                const declaration = z3.Z3_model_get_const_decl(self.z3_context, model, @intCast(i)) orelse @panic("Z3_model_get_const_decl failed");

                const num_args = 0;
                const args = null;
                const app = z3.Z3_mk_app(self.z3_context, declaration, num_args, args) orelse @panic("Z3_mk_app failed");

                const model_completion = true;
                var result: z3.Z3_ast = undefined;
                const success = z3.Z3_model_eval(self.z3_context, model, app, model_completion, &result);
                if (!success) return error.modelcheckingFailed;

                const result_kind = z3.Z3_get_ast_kind(self.z3_context, result);
                const value = switch (result_kind) {
                    z3.Z3_NUMERAL_AST => z3.Z3_get_numeral_string(self.z3_context, result),
                    else => return error.unsupportedType,
                };

                const name = z3.Z3_get_decl_name(self.z3_context, declaration) orelse @panic("Z3_get_decl_name failed");
                const kind = z3.Z3_get_symbol_kind(self.z3_context, name);
                switch (kind) {
                    z3.Z3_INT_SYMBOL => {
                        const id = z3.Z3_get_symbol_int(self.z3_context, name);
                        std.log.info("x{d} = {s}", .{ id, value });
                    },
                    z3.Z3_STRING_SYMBOL => {
                        const id = z3.Z3_get_symbol_string(self.z3_context, name);
                        std.log.info("{s} = {s}", .{ id, value });
                    },
                    else => return error.unsupportedType,
                }
            }

            return true;
        },
        // not satisfiable
        z3.Z3_L_FALSE => {
            std.log.info("No issues found", .{});
            return false;
        },
        else => @panic("invalid Z3_solver_check result"),
    }
}

pub fn renderConstraint(self: *@This(), constraint: *const Model.Constraint) !void {
    // FIXME: support left hand side literal
    if (constraint.left != .reference) return error.unexpectedType;

    const left = constraint.left.reference;
    const right = constraint.right;
    const left_ast = self.symbol_map.get(left.id) orelse @panic("symbol not found");

    // FIXME: support other comparisons
    if (constraint.comparison != .equal) std.log.warn("Z3 comparison not integrated yet", .{});

    switch (right) {
        .reference => {
            const right_ast = self.symbol_map.get(left.id) orelse @panic("symbol not found");
            const eq = z3.Z3_mk_eq(self.z3_context, left_ast, right_ast) orelse @panic("z3.Z3_mk_eq failed");
            z3.Z3_solver_assert(self.z3_context, self.z3_solver, eq);
        },
        .literal => |literal| {
            // if (std.mem.eql(u8, literal, "undefined")) return self.addError(@src(), error.unexpectedType);
            if (std.mem.eql(u8, literal, "undefined")) return error.unexpectedType;

            // FIXME: literal is not necessarily an integer
            // These are only added for debugging reason, so it's easier to know the original variable
            const value = std.fmt.parseInt(usize, literal, 10) catch {
                std.log.err("Unsupported literal, dropping constraint: {s} = x{d}", .{ literal, left.id });
                return;
            };
            const right_ast = z3.Z3_mk_int64(self.z3_context, @intCast(value), self.z3_int_sort);
            const eq = z3.Z3_mk_eq(self.z3_context, left_ast, right_ast) orelse @panic("z3.Z3_mk_eq failed");
            z3.Z3_solver_assert(self.z3_context, self.z3_solver, eq);
        },
        // .type_identifier => return self.addError(@src(), error.unexpectedType),
        .type_identifier => return error.unexpectedType,
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
