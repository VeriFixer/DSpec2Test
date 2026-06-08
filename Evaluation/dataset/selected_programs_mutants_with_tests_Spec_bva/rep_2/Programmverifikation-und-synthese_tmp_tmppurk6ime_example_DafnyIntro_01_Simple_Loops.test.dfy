
method {:test} Test12() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(101);
expect r0 == 101 * (101 + 1) / 2;
}
method {:test} Test13() {
var r0 := sumOdds(101);
expect r0 == 101 * 101;
}

// REPEAT 2 - TIME: 10.3909107 s