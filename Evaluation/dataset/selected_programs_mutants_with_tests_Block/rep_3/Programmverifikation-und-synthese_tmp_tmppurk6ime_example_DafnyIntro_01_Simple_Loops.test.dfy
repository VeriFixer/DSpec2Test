
method {:test} Test4() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(3);
expect r0 == 3 * (3 + 1) / 2;
}
method {:test} Test5() {
var r0 := sumOdds(3);
expect r0 == 3 * 3;
}

// REPEAT 3 - TIME: 4.5857464 s