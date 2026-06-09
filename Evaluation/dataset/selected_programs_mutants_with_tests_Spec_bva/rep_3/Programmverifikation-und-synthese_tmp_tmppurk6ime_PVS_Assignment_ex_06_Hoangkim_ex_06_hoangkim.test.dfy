
method {:test} Test11() {
expect 16757 > 0 && 8378 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16757, 8378);
}

// REPEAT 3 - TIME: 8.4658511 s