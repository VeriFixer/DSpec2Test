
method {:test} Test3() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(3);
expect r0 == 3 * (7 * 3 - 5) / 2;
}

// REPEAT 4 - TIME: 5.2449848 s