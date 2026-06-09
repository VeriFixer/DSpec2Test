
method {:test} Test18() {
expect 246338 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(246337, 246338);
expect r1 * 246338 + r0 == 246337 && 0 <= r0 < 246338 && 0 <= r1;
}

// REPEAT 9 - TIME: 12.3375812 s