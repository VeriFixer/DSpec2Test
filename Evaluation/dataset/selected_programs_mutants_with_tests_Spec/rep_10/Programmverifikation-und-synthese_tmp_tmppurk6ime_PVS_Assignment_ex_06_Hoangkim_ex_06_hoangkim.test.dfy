
method {:test} Test9() {
expect 16921 > 0 && 8460 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16921, 8460);
}

// REPEAT 10 - TIME: 12.2895442 s