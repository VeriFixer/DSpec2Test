
method {:test} Test6() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(101);
expect r0 == 101 * (3 * 101 - 2);
}

// REPEAT 2 - TIME: 6.0488059 s