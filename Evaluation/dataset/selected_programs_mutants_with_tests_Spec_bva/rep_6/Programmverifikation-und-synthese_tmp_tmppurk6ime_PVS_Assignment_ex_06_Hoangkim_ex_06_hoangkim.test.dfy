
method {:test} Test14() {
expect 16838 > 0 && 8419 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16838, 8419);
}

// REPEAT 6 - TIME: 13.4732076 s