
method {:test} Test14() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(102);
expect r0 == 102 * (102 + 1) / 2;
}
method {:test} Test15() {
var r0 := sumOdds(102);
expect r0 == 102 * 102;
}

// REPEAT 3 - TIME: 9.9360801 s