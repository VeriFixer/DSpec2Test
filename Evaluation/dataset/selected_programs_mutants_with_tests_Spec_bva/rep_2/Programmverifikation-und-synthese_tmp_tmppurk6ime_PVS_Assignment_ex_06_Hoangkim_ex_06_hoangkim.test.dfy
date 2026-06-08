
method {:test} Test10() {
expect 16754 > 0 && 8377 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16754, 8377);
}

// REPEAT 2 - TIME: 9.4265018 s