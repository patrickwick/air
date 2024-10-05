const std = @import("std");

const Tokenizer = @import("Tokenizer.zig");
const Token = Tokenizer.Token;

pub const RefereceId = u32;

pub const Reference = struct {
    is_unreferenced: bool,
    id: RefereceId,
};

pub const Argument = union(enum) {
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

pub fn reference(tokenizer: anytype) !Reference {
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

pub fn expression(context: anytype, ref: Reference, instruction_token: Token) !void {
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
            try context.addEquivalence(store_target, source);
        },
        // %13 = load(usize, %4!)
        // %3 = load([][*:0]u8, <*[][*:0]u8, os.argv>)
        .load => {
            // TODO: use data type
            try skipType(tokenizer);
            if (tokenizer.nextToken() != Token.comma) return error.unexpectedToken;

            if (tokenizer.lookaheadToken() == Token.percent) {
                const source = try reference(tokenizer);
                try context.addEquivalence(ref, Argument{ .reference = source });
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

            try context.addConstraint(Argument{ .reference = ref }, argument_name, .equal, false);
        },
        // %15 = sub_safe(%13!, <usize, 100>)
        .sub_safe => {
            const first = try argument(tokenizer);
            if (tokenizer.nextToken() != Token.comma) return error.unexpectedToken;
            const second = try argument(tokenizer);
            try context.addOperation(ref, first, second, .minus);
        },
        .mul_safe => {
            const first = try argument(tokenizer);
            if (tokenizer.nextToken() != Token.comma) return error.unexpectedToken;
            const second = try argument(tokenizer);
            try context.addOperation(ref, first, second, .multiply);
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
            try context.addOperation(ref, first, second, .plus);
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
            try context.addConstraint(first, second, .greater, true);
            try context.addOperation(ref, first, second, .minus);
        },
        // %7 = mul_with_overflow(struct{usize, u1}, %5!, <usize, 2>)
        .mul_with_overflow => {
            try skipType(tokenizer);
            if (tokenizer.nextToken() != Token.comma) return error.unexpectedToken;

            const first = try argument(tokenizer);
            if (tokenizer.nextToken() != Token.comma) return error.unexpectedToken;
            const second = try argument(tokenizer);
            try context.addOperation(ref, first, second, .multiply);
        },
        // %23 = div_trunc(<usize, 123>, %15!)
        // %54 = div_trunc(@Air.Inst.Ref.one_usize, %46!)
        .div_trunc => {
            const first = try argument(tokenizer);
            if (tokenizer.nextToken() != Token.comma) return error.unexpectedToken;
            const second = try reference(tokenizer);
            // Add constraint that there cannot be a division by zero
            try context.writer.print("# division by zero checked\n", .{});
            try context.addConstraint(Argument{ .reference = second }, Argument{ .literal = "0" }, .equal, true);
            try context.addOperation(ref, first, Argument{ .reference = second }, .divide);
        },
        // %32 = struct_field_val(%24!, 0)
        .struct_field_val => {
            const source = try reference(tokenizer);
            if (tokenizer.nextToken() != Token.comma) return error.unexpectedToken;

            // TODO: hardcoded to only select the first field of the struct since the second field is a success bool
            const identifier = tokenizer.nextToken();
            if (identifier != Token.identifier) return error.unexpectedToken;
            if (std.mem.eql(u8, identifier.identifier, "0")) {
                try context.addEquivalence(ref, Argument{ .reference = source });
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
