
method {:test} Test4() {
expect 30886 > 0 && 11583 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(30886, 11583);
}

// REPEAT 5 - TIME: 23.0913442 s