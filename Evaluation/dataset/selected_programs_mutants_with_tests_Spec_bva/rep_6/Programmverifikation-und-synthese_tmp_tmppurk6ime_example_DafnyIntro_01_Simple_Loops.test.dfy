
method {:test} Test20() {
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(105);
expect r0 == 105 * (105 + 1) / 2;
}
method {:test} Test21() {
var r0 := sumOdds(105);
expect r0 == 105 * 105;
}

// REPEAT 6 - TIME: 12.7436188 s