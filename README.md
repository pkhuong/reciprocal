Baseline implementation of division by constants
================================================
[![Build Status](https://app.travis-ci.com/pkhuong/reciprocal.svg?branch=main)](https://app.travis-ci.com/pkhuong/reciprocal) [![Coverage Status](https://coveralls.io/repos/github/pkhuong/reciprocal/badge.svg?branch=main)](https://coveralls.io/github/pkhuong/reciprocal?branch=main)

When dividing integers by compile-time constants, compilers (LLVM) can
be trusted to convert those to a sequence of multiplication and shift.

That doesn't work so well when the constant isn't known until runtime.

This crate implements a simple strategy with reliable performance.
Does reliable imply good?
[For this application, it does.](https://pvk.ca/Blog/2021/05/14/baseline-implementations-should-be-predictable/)

The basic `PartialReciprocal` should be compiled to a constant-time
fast path, and can handle every divisor except 0, 1, and `u64::MAX`.

The slightly more complex `Reciprocal` can also divide by 1 and
`u64::MAX`, at the expense of one more `u64` field, and a slightly
more complex (one more load, maybe one more integer arithmetic
instruction) fast path.
