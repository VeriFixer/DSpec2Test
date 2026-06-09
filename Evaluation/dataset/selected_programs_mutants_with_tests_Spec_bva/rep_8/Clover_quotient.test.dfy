
method {:test} Test17() {
expect 246337 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(246336, 246337);
expect r1 * 246337 + r0 == 246336 && 0 <= r0 < 246337 && 0 <= r1;
}

// REPEAT 8 - TIME: 11.7021472 s