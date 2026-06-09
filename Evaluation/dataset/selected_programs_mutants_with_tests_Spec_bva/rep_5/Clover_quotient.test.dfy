
method {:test} Test14() {
expect 246334 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(246333, 246334);
expect r1 * 246334 + r0 == 246333 && 0 <= r0 < 246334 && 0 <= r1;
}

// REPEAT 5 - TIME: 9.8756243 s