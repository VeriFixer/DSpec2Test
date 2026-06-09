
method {:test} Test8() {
expect 9 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(8, 9);
expect r1 * 9 + r0 == 8 && 0 <= r0 < 9 && 0 <= r1;
}

// REPEAT 9 - TIME: 19.938924 s