
method {:test} Test4() {
expect 5 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(4, 5);
expect r1 * 5 + r0 == 4 && 0 <= r0 < 5 && 0 <= r1;
}

// REPEAT 5 - TIME: 5.4195643 s