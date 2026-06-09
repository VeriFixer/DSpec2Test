
method {:test} Test16() {
expect 83093 > 0 && 40928 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(83093, 40928);
}
method {:test} Test17() {
expect 84294 > 0 && 40928 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(84294, 40928);
}

// REPEAT 9 - TIME: 11.9862836 s