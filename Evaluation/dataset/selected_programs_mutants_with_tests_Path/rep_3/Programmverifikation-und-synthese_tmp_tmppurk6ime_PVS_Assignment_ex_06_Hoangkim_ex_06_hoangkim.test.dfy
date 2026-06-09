
method {:test} Test2() {
expect 7725 > 0 && 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(7725, 3);
}

// REPEAT 3 - TIME: 15.1151079 s