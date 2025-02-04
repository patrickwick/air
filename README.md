# Zig AIR Validation Experiment

Experiment in generating Z3 expressions from Zig analyzed intermediate representation (AIR).
The idea is that function precondition violation can be found using an SMT solver.
Here, a simple code snippet that causes division by zero is used as an example.

Analyzing the following snippet will yield the result that division by zero occurs if `c == 50`:

```zig
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
```

Model:

```
Result:
sat

Expression:
(declare-fun x1 () Int)
(assert (or (> (* x1 2) 100) (= (- (* x1 2) 100) 0) (> (* x1 2) 100)))
(assert and)
(model-add x1 () Int 50)

Model:
[x1 = 50]
```

I know that parsing the textual representation from --verbose-air is not great but working on the binary format either requires compiling the compiler repeatedly or writing a binary dump for AIR.
I started writing a binary dump for AIR but parsing the textual representation is good enough for a crude PoC.

**Update:** check out [CLR](https://github.com/ityonemo/clr) for a PoC that implements a borrow checker using the same AIR analysis approach that has appeared meanwhile!
