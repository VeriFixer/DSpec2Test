
method {:test} Test3() {
expect 4 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(3, 4);
expect r1 * 4 + r0 == 3 && 0 <= r0 < 4 && 0 <= r1;
}

// REPEAT 4 - TIME: 5.6016231 s