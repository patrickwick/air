const std = @import("std");

pub const StringView = []const u8;

pub const endOfFileCharacter: u8 = 0;
pub const newLineCharacter: u8 = '\n';

pub const Token = union(enum) {
    endOfFile: void,

    semicolon: void,
    comma: void,
    colon: void,
    percent: void,
    dot: void,
    bracketOpen: void,
    bracketClose: void,
    curlyOpen: void,
    curlyClose: void,
    squareOpen: void,
    squareClose: void,

    less: void,
    greater: void,
    caret: void,
    exclamation: void,
    equal: void,
    plus: void,
    minus: void,
    star: void,
    hash: void,
    quote: void,

    forwardSlash: void,

    comment: StringView,
    blockComment: StringView,

    identifier: StringView,
    stringLiteral: StringView,
    numberLiteral: usize,

    returnToken: void,
    auto: void,
    constToken: void,
    varToken: void,
    function: void,

    // AIR instructions
    alloc: void,
    store_safe: void,
    load: void,
    arg: void,
    struct_field_val: void,

    // AIR operators
    add_safe: void,
    sub_safe: void,
    mul_safe: void,
    add_with_overflow: void,
    sub_with_overflow: void,
    mul_with_overflow: void,
    div_trunc: void,

    // AIR types
    struct_type: void,

    // AIR debug
    dbg_var_val: void,
    dbg_var_ptr: void,

    pub fn format(self: @This(), comptime fmt: []const u8, options: std.fmt.FormatOptions, writer: anytype) !void {
        _ = fmt;
        _ = options;
        return switch (self) {
            .comment => writer.print("{s}: '//{s}'", .{ @tagName(self), self.comment }),
            .blockComment => writer.print("{s}: /*{s}*/", .{ @tagName(self), self.blockComment }),
            .identifier => writer.print("{s}: '{s}'", .{ @tagName(self), self.identifier }),
            else => writer.print("{s}", .{@tagName(self)}),
        };
    }
};

pub const TokenizerSourceLocation = struct {
    line: u32,
    column: u32,
    code_line: []const u8,
};

pub const IncrementalTokenizer = struct {
    offset: usize = 0,
    source: StringView,

    pub fn deinit(_: *@This()) void {}

    pub fn nextToken(self: *@This()) Token {
        _ = self.extract(isWhitespace);
        defer self.next();
        const token = switch (self.lookahead(0)) {
            // single character
            endOfFileCharacter => Token.endOfFile,
            ';' => Token.semicolon,
            ',' => Token.comma,
            '%' => Token.percent,
            '.' => Token.dot,
            ':' => Token.colon,
            '(' => Token.bracketOpen,
            ')' => Token.bracketClose,
            '{' => Token.curlyOpen,
            '}' => Token.curlyClose,
            '[' => Token.squareOpen,
            ']' => Token.squareClose,
            '<' => Token.less,
            '>' => Token.greater,
            '^' => Token.caret,
            '!' => Token.exclamation,
            '=' => Token.equal,
            '+' => Token.plus,
            '-' => Token.minus,
            '*' => Token.star,
            '#' => Token.hash,
            '"' => Token.quote,
            // two characters
            '/' => switch (self.lookahead(1)) {
                '/' => Token{ .comment = self.extract(isLineComment)[2..] },
                '*' => Token{ .blockComment = self.extract(isBlockComment)[2..] },
                else => Token.forwardSlash,
            },
            // multi character
            else => token: {
                const tokenSlice = self.extract(isToken);

                // ordered by frequency
                if (std.mem.eql(u8, tokenSlice, "fn")) break :token Token.varToken;
                if (std.mem.eql(u8, tokenSlice, "const")) break :token Token.constToken;
                if (std.mem.eql(u8, tokenSlice, "var")) break :token Token.varToken;
                if (std.mem.eql(u8, tokenSlice, "return")) break :token Token.returnToken;
                if (std.mem.eql(u8, tokenSlice, "auto")) break :token Token.auto;

                // AIR instructions
                if (std.mem.eql(u8, tokenSlice, "alloc")) break :token Token.alloc;
                if (std.mem.eql(u8, tokenSlice, "store_safe")) break :token Token.store_safe;
                if (std.mem.eql(u8, tokenSlice, "load")) break :token Token.load;
                if (std.mem.eql(u8, tokenSlice, "arg")) break :token Token.arg;
                if (std.mem.eql(u8, tokenSlice, "struct_field_val")) break :token Token.struct_field_val;
                // AIR operators
                if (std.mem.eql(u8, tokenSlice, "add_safe")) break :token Token.add_safe;
                if (std.mem.eql(u8, tokenSlice, "sub_safe")) break :token Token.sub_safe;
                if (std.mem.eql(u8, tokenSlice, "mul_safe")) break :token Token.mul_safe;
                if (std.mem.eql(u8, tokenSlice, "add_with_overflow")) break :token Token.add_with_overflow;
                if (std.mem.eql(u8, tokenSlice, "sub_with_overflow")) break :token Token.sub_with_overflow;
                if (std.mem.eql(u8, tokenSlice, "mul_with_overflow")) break :token Token.mul_with_overflow;
                if (std.mem.eql(u8, tokenSlice, "div_trunc")) break :token Token.div_trunc;

                // AIR types
                if (std.mem.eql(u8, tokenSlice, "struct")) break :token Token.struct_type;

                // AIR debug
                if (std.mem.eql(u8, tokenSlice, "dbg_var_val")) break :token Token.dbg_var_val;
                if (std.mem.eql(u8, tokenSlice, "dbg_var_ptr")) break :token Token.dbg_var_ptr;

                break :token Token{ .identifier = tokenSlice };
            },
        };

        // std.log.debug("{}", .{token});
        return token;
    }

    pub fn lookaheadToken(self: *@This()) Token {
        const previous_offset = self.offset;
        const token = self.nextToken();
        self.offset = previous_offset;
        return token;
    }

    pub fn getCurrentSourceLocation(self: *@This()) TokenizerSourceLocation {
        // NOTE: slow counting of newlines in case of errors instead of overhead in the happy path
        var line: u32 = 1;
        var column: u32 = 0;
        var start: usize = 0;
        var end: usize = self.source.len - 1;

        const split_index = @min(self.source.len - 1, self.offset + 1);
        for (self.source, 0..) |char, i| {
            if (char == newLineCharacter) {
                if (i < split_index) {
                    line += 1;
                    column = 0;
                    start = i + 1;
                } else {
                    end = i;
                    break;
                }
            }
            if (i < split_index) column += 1;
        }

        return TokenizerSourceLocation{
            .line = line,
            .column = column,
            .code_line = self.source[start..end],
        };
    }

    inline fn lookahead(self: @This(), comptime count: usize) u8 {
        return if (self.source.len > self.offset + count) self.source[self.offset + count] else endOfFileCharacter;
    }

    inline fn next(self: *@This()) void {
        self.*.offset += 1;
    }

    const ConditionFunction = fn (@This()) callconv(.Inline) bool;
    inline fn extract(self: *@This(), comptime condition: ConditionFunction) StringView {
        const start = self.offset;
        while (condition(self.*)) : (self.next()) {}
        return self.source[start..@min(self.offset + 1, self.source.len)];
    }

    inline fn isWhitespace(self: @This()) bool {
        return switch (self.lookahead(0)) {
            ' ', '\t', newLineCharacter => true,
            else => false,
        };
    }

    inline fn isLineComment(self: @This()) bool {
        return self.lookahead(1) != newLineCharacter;
    }

    inline fn isBlockComment(self: @This()) bool {
        return self.lookahead(1) != '*' or self.lookahead(2) != '/';
    }

    inline fn isToken(self: @This()) bool {
        return switch (self.lookahead(1)) {
            'a'...'z', 'A'...'Z', '0'...'9', '_', '-' => true,
            else => false,
        };
    }
};

const t = std.testing;

test "Whitespaces" {
    const code = " \t  \n\n const  \t\t\n; \t\n";
    var tokenizer = IncrementalTokenizer{ .source = code };
    defer tokenizer.deinit();

    try t.expectEqual(.constToken, tokenizer.nextToken());
    try t.expectEqual(.semicolon, tokenizer.nextToken());
}
