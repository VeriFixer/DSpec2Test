
method {:test} Test18() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(9);
expect r0 == 9 * (9 + 1) / 2;
}
method {:test} Test19() {
var r0 := sumOdds(9);
expect r0 == 9 * 9;
}

// REPEAT 10 - TIME: 44.313593 s