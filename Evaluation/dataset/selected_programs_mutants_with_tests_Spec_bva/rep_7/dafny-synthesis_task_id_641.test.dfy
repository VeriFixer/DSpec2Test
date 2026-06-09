
method {:test} Test11() {
expect 341796878 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(341796878);
expect r0 == 341796878 * (7 * 341796878 - 5) / 2;
}

// REPEAT 7 - TIME: 38.940562 s