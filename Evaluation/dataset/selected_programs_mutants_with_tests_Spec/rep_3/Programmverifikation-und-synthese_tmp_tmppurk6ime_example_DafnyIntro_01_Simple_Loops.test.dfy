
method {:test} Test4() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(2);
expect r0 == 2 * (2 + 1) / 2;
}
method {:test} Test5() {
var r0 := sumOdds(2);
expect r0 == 2 * 2;
}

// REPEAT 3 - TIME: 6.4338705 s