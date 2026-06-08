
method {:test} Test8() {
expect 46328 > 0 && 23164 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(46328, 23164);
}

// REPEAT 9 - TIME: 34.1186278 s