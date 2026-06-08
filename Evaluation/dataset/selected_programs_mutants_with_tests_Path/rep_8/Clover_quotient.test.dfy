
method {:test} Test7() {
expect 8 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(7, 8);
expect r1 * 8 + r0 == 7 && 0 <= r0 < 8 && 0 <= r1;
}

// REPEAT 8 - TIME: 27.0521789 s