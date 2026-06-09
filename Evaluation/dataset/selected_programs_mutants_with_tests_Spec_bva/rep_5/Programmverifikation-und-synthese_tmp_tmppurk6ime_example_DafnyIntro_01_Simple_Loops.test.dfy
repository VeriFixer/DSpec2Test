
method {:test} Test18() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(104);
expect r0 == 104 * (104 + 1) / 2;
}
method {:test} Test19() {
var r0 := sumOdds(104);
expect r0 == 104 * 104;
}

// REPEAT 5 - TIME: 11.8354868 s