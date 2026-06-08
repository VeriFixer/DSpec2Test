
method {:test} Test7() {
expect 30889 > 0 && 11586 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(30889, 11586);
}

// REPEAT 8 - TIME: 30.8939002 s