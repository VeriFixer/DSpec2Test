
method {:test} Test8() {
expect 0 < 9 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(9);
}

// REPEAT 9 - TIME: 10.2645507 s