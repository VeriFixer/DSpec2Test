
method {:test} Test22() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(106);
expect r0 == 106 * (106 + 1) / 2;
}
method {:test} Test23() {
var r0 := sumOdds(106);
expect r0 == 106 * 106;
}

// REPEAT 7 - TIME: 16.340698 s