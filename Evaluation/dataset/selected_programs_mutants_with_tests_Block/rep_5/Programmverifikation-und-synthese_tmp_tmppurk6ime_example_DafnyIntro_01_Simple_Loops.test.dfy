
method {:test} Test8() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(5);
expect r0 == 5 * (5 + 1) / 2;
}
method {:test} Test9() {
var r0 := sumOdds(5);
expect r0 == 5 * 5;
}

// REPEAT 5 - TIME: 6.7646068 s