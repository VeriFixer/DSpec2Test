
method {:test} Test7() {
expect 0 < 8 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(8);
}

// REPEAT 8 - TIME: 9.5153458 s