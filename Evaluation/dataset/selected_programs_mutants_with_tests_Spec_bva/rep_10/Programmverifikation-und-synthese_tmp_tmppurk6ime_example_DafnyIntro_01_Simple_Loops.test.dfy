
method {:test} Test28() {
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(109);
expect r0 == 109 * (109 + 1) / 2;
}
method {:test} Test29() {
var r0 := sumOdds(109);
expect r0 == 109 * 109;
}

// REPEAT 10 - TIME: 18.6505633 s