
method {:test} Test18() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(10);
expect r0 == 10 * (10 + 1) / 2;
}
method {:test} Test19() {
var r0 := sumOdds(10);
expect r0 == 10 * 10;
}

// REPEAT 10 - TIME: 11.2025012 s