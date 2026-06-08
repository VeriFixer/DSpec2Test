
method {:test} Test9() {
expect 7729 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(7729, 7729);
expect r1 * 7729 + r0 == 7729 && 0 <= r0 < 7729 && 0 <= r1;
}

// REPEAT 10 - TIME: 8.2141682 s