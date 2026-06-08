
method {:test} Test6() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(4);
expect r0 == 4 * (4 + 1) / 2;
}
method {:test} Test7() {
var r0 := sumOdds(4);
expect r0 == 4 * 4;
}

// REPEAT 4 - TIME: 5.9724827 s