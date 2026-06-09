
method {:test} Test6() {
expect 30888 > 0 && 11585 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(30888, 11585);
}

// REPEAT 7 - TIME: 30.6541859 s