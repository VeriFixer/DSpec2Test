
method {:test} Test12() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(7);
expect r0 == 7 * (7 + 1) / 2;
}
method {:test} Test13() {
var r0 := sumOdds(7);
expect r0 == 7 * 7;
}

// REPEAT 7 - TIME: 8.8140443 s