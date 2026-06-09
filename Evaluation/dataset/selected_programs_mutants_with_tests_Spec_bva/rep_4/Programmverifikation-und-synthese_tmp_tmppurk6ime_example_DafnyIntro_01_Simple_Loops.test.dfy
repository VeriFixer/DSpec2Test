
method {:test} Test16() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(103);
expect r0 == 103 * (103 + 1) / 2;
}
method {:test} Test17() {
var r0 := sumOdds(103);
expect r0 == 103 * 103;
}

// REPEAT 4 - TIME: 10.8450803 s