
method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(1);
expect r0 == 4 * 1 * 1 - 3 * 1;
}

// REPEAT 2 - TIME: 3.442139 s