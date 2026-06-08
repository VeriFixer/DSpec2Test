
method {:test} Test12() {
expect 16759 > 0 && 8379 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16759, 8379);
}

// REPEAT 4 - TIME: 11.4650058 s