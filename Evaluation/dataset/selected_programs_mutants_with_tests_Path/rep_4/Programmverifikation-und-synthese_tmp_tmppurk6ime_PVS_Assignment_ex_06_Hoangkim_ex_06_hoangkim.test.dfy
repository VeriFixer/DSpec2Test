
method {:test} Test3() {
expect 23164 > 0 && 11582 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(23164, 11582);
}

// REPEAT 4 - TIME: 17.1263593 s