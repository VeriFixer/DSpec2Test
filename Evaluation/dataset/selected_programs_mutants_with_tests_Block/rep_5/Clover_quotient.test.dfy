
method {:test} Test4() {
expect 7724 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(7724, 7724);
expect r1 * 7724 + r0 == 7724 && 0 <= r0 < 7724 && 0 <= r1;
}

// REPEAT 5 - TIME: 4.6258167 s