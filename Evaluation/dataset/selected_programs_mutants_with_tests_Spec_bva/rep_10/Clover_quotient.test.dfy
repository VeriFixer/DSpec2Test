
method {:test} Test19() {
expect 246339 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(246338, 246339);
expect r1 * 246339 + r0 == 246338 && 0 <= r0 < 246339 && 0 <= r1;
}

// REPEAT 10 - TIME: 12.9937731 s