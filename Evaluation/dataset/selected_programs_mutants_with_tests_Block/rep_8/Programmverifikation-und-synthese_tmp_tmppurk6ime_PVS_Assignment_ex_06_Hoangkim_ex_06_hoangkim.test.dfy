
method {:test} Test14() {
expect 81854 > 0 && 40927 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(81854, 40927);
}
method {:test} Test15() {
expect 66415 > 0 && 28780 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(66415, 28780);
}

// REPEAT 8 - TIME: 11.249433 s