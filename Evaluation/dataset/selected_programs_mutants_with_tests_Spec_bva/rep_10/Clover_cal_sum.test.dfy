
method {:test} Test14() {
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(109);
expect r0 == 109 * (109 + 1) / 2;
}

// REPEAT 10 - TIME: 11.6305277 s