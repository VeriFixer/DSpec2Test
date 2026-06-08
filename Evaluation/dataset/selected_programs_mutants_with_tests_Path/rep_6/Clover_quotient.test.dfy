
method {:test} Test5() {
expect 6 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(5, 6);
expect r1 * 6 + r0 == 5 && 0 <= r0 < 6 && 0 <= r1;
}

// REPEAT 6 - TIME: 21.7797452 s