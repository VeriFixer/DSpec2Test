
method {:test} Test12() {
expect 65278 > 0 && 28779 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(65278, 28779);
}
method {:test} Test13() {
expect 66414 > 0 && 28779 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(66414, 28779);
}

// REPEAT 7 - TIME: 9.9493529 s