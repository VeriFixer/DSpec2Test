
method {:test} Test6() {
expect 16839 > 0 && 8419 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16839, 8419);
}

// REPEAT 7 - TIME: 9.6963526 s