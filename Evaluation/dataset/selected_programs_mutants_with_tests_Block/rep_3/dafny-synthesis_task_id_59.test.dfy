
method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(2);
expect r0 == 2 * (3 * 2 - 2);
}

// REPEAT 3 - TIME: 3.4973399 s