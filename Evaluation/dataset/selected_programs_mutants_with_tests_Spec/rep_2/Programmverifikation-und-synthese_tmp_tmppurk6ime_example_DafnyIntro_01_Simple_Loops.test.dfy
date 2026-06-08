
method {:test} Test2() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(1);
expect r0 == 1 * (1 + 1) / 2;
}
method {:test} Test3() {
var r0 := sumOdds(1);
expect r0 == 1 * 1;
}

// REPEAT 2 - TIME: 5.0370203 s