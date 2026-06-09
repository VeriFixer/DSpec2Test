
method {:test} Test15() {
expect 16840 > 0 && 8420 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16840, 8420);
}

// REPEAT 7 - TIME: 11.6030967 s