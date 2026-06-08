
method {:test} Test5() {
expect 7725 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(7725, 7725);
expect r1 * 7725 + r0 == 7725 && 0 <= r0 < 7725 && 0 <= r1;
}

// REPEAT 6 - TIME: 5.338976 s