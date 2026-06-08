
method {:test} Test10() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(5);
expect r0 == 5 * (5 + 1) / 2;
}
method {:test} Test11() {
var r0 := sumOdds(5);
expect r0 == 5 * 5;
}

// REPEAT 6 - TIME: 10.6975943 s