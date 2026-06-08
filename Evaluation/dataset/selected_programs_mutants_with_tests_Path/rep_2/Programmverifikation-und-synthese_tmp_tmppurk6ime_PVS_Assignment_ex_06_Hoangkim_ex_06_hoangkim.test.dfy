
method {:test} Test1() {
expect 7724 > 0 && 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(7724, 2);
}

// REPEAT 2 - TIME: 10.6153933 s