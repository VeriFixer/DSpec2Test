
method {:test} Test9() {
expect 10 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(9, 10);
expect r1 * 10 + r0 == 9 && 0 <= r0 < 10 && 0 <= r1;
}

// REPEAT 10 - TIME: 22.2164136 s