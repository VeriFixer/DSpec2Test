
method {:test} Test12() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(6);
expect r0 == 6 * (6 + 1) / 2;
}
method {:test} Test13() {
var r0 := sumOdds(6);
expect r0 == 6 * 6;
}

// REPEAT 7 - TIME: 9.8991086 s