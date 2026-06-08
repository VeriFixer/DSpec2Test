
method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(2);
expect r0 == 2 * (2 + 1) / 2;
}
method {:test} Test3() {
var r0 := sumOdds(2);
expect r0 == 2 * 2;
}

// REPEAT 2 - TIME: 3.7318103 s