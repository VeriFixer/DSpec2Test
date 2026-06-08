
method {:test} Test2() {
expect 0 < 42 <= 42, "If this check fails at runtime, the test does not meet the preconditions";
BigFoot(42);
}

// REPEAT 3 - TIME: 4.777046 s