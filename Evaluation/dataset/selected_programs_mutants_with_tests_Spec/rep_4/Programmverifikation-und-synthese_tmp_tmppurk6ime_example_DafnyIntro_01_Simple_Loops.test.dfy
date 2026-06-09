
method {:test} Test6() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(3);
expect r0 == 3 * (3 + 1) / 2;
}
method {:test} Test7() {
var r0 := sumOdds(3);
expect r0 == 3 * 3;
}

// REPEAT 4 - TIME: 6.601775 s