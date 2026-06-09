
method {:test} Test8() {
expect 7728 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(7728, 7728);
expect r1 * 7728 + r0 == 7728 && 0 <= r0 < 7728 && 0 <= r1;
}

// REPEAT 9 - TIME: 7.1904147 s