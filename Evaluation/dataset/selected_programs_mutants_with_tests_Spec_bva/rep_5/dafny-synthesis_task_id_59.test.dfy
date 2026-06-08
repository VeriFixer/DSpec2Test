
method {:test} Test9() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(104);
expect r0 == 104 * (3 * 104 - 2);
}

// REPEAT 5 - TIME: 9.1270955 s