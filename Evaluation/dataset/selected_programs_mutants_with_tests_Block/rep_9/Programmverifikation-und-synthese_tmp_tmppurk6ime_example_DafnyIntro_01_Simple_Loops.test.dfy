
method {:test} Test16() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(9);
expect r0 == 9 * (9 + 1) / 2;
}
method {:test} Test17() {
var r0 := sumOdds(9);
expect r0 == 9 * 9;
}

// REPEAT 9 - TIME: 10.0212091 s