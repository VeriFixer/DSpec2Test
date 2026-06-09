
method {:test} Test9() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(104);
expect r0 == 4 * 104 * 104 - 3 * 104;
}

// REPEAT 5 - TIME: 7.827063 s