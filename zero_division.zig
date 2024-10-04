// Example application for generating verbose AIR using a compiler debug build:
// ../zig/build/stage3/bin/zig build-exe --verbose-air ./zero_division.zig 2> air
const std = @import("std");

fn divide(a: usize, b: usize) usize {
    // const c = a - b * b + 16; // zero division and underflow possible
    return a / b;
}

pub fn main() !void {
    var c: usize = undefined;
    c *= 2;

    var e: usize = 20;
    e *= 5;

    const result = 2 / (c - e);
    _ = result;
    _ = divide(2, c - e);
}

test {
    std.testing.refAllDecls(@This());
}
