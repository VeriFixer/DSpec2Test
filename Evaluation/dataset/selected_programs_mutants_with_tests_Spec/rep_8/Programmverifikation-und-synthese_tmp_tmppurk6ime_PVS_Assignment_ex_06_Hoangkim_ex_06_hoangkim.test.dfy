
method {:test} Test7() {
expect 16841 > 0 && 8420 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16841, 8420);
}

// REPEAT 8 - TIME: 10.6187454 s