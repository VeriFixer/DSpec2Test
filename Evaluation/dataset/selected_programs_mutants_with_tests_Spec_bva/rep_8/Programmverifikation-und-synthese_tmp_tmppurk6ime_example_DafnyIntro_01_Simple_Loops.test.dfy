
method {:test} Test24() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(107);
expect r0 == 107 * (107 + 1) / 2;
}
method {:test} Test25() {
var r0 := sumOdds(107);
expect r0 == 107 * 107;
}

// REPEAT 8 - TIME: 14.4154145 s