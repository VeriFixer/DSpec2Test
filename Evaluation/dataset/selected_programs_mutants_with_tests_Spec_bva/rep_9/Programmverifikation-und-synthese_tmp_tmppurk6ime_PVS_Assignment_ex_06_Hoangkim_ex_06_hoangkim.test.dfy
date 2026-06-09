
method {:test} Test17() {
expect 16845 > 0 && 8422 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16845, 8422);
}

// REPEAT 9 - TIME: 13.1368292 s