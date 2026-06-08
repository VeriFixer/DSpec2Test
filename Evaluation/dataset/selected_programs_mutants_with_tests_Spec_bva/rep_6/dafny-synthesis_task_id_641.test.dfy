
method {:test} Test10() {
expect 341796877 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(341796877);
expect r0 == 341796877 * (7 * 341796877 - 5) / 2;
}

// REPEAT 6 - TIME: 38.5846746 s