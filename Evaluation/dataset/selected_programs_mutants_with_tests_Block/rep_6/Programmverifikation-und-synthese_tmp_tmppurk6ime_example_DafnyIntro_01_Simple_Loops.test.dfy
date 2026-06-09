
method {:test} Test10() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(6);
expect r0 == 6 * (6 + 1) / 2;
}
method {:test} Test11() {
var r0 := sumOdds(6);
expect r0 == 6 * 6;
}

// REPEAT 6 - TIME: 7.6533173 s