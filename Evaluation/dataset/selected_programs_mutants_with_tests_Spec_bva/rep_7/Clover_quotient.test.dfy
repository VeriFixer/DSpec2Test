
method {:test} Test16() {
expect 246336 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(246335, 246336);
expect r1 * 246336 + r0 == 246335 && 0 <= r0 < 246336 && 0 <= r1;
}

// REPEAT 7 - TIME: 11.1272833 s