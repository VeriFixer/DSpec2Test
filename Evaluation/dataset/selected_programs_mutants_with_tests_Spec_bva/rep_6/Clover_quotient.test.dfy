
method {:test} Test15() {
expect 246335 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(246334, 246335);
expect r1 * 246335 + r0 == 246334 && 0 <= r0 < 246335 && 0 <= r1;
}

// REPEAT 6 - TIME: 10.502687 s