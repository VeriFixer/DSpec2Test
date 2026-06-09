
method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(2);
expect r0 == 2 * (7 * 2 - 5) / 2;
}

// REPEAT 3 - TIME: 4.1230263 s