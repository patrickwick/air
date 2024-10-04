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
