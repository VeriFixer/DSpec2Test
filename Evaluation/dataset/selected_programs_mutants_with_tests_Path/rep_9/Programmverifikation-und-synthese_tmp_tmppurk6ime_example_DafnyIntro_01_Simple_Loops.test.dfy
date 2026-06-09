
method {:test} Test16() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(8);
expect r0 == 8 * (8 + 1) / 2;
}
method {:test} Test17() {
var r0 := sumOdds(8);
expect r0 == 8 * 8;
}

// REPEAT 9 - TIME: 42.3844151 s