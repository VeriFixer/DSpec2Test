
method {:test} Test18() {
expect 99734 > 0 && 49867 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(99734, 49867);
}
method {:test} Test19() {
expect 84295 > 0 && 40929 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(84295, 40929);
}

// REPEAT 10 - TIME: 13.1252229 s