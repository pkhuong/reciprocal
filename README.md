Baseline implementation of division by constants
================================================

When dividing integers by compile-time constants, compilers (LLVM) can
be trusted to convert those to a sequence of multiplication and shift.

That doesn't work so well when the constant isn't known until runtime.

This crate implements a simple strategy with reliable performance.

The basic `PartialReciprocal` should be compiled to a constant-time
fast path, and can handle every divisor except 0, 1, and `u64::MAX`.

The slightly more complex `Reciprocal` can also divide by 1 and
`u64::MAX`, at the expense of one branch in the fast path: we must
treat divisions *of* `u64::MAX` specially.
