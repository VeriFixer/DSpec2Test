
method {:test} Test11() {
expect 102 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(246330, 102);
expect r1 * 102 + r0 == 246330 && 0 <= r0 < 102 && 0 <= r1;
}

// REPEAT 2 - TIME: 8.3794464 s