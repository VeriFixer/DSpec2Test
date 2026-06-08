
method {:test} Test26() {
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(108);
expect r0 == 108 * (108 + 1) / 2;
}
method {:test} Test27() {
var r0 := sumOdds(108);
expect r0 == 108 * 108;
}

// REPEAT 9 - TIME: 17.9116691 s