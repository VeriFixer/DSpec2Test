
method {:test} Test3() {
expect 16756 > 0 && 8378 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16756, 8378);
}

// REPEAT 4 - TIME: 7.100238 s