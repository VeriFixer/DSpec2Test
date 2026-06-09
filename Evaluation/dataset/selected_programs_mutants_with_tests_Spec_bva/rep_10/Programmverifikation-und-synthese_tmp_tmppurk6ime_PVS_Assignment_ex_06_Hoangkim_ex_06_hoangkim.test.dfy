
method {:test} Test18() {
expect 16847 > 0 && 8423 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16847, 8423);
}

// REPEAT 10 - TIME: 13.7589895 s