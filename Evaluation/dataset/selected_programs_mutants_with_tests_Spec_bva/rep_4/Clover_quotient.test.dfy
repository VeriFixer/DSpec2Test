
method {:test} Test13() {
expect 246333 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(246332, 246333);
expect r1 * 246333 + r0 == 246332 && 0 <= r0 < 246333 && 0 <= r1;
}

// REPEAT 4 - TIME: 9.2737505 s