
method {:test} Test7() {
expect 7727 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(7727, 7727);
expect r1 * 7727 + r0 == 7727 && 0 <= r0 < 7727 && 0 <= r1;
}

// REPEAT 8 - TIME: 6.5371472 s