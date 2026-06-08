
method {:test} Test14() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(7);
expect r0 == 7 * (7 + 1) / 2;
}
method {:test} Test15() {
var r0 := sumOdds(7);
expect r0 == 7 * 7;
}

// REPEAT 8 - TIME: 36.1140762 s