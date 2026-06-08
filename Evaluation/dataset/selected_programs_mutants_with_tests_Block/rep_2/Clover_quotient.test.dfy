
method {:test} Test1() {
expect 7721 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(7721, 7721);
expect r1 * 7721 + r0 == 7721 && 0 <= r0 < 7721 && 0 <= r1;
}

// REPEAT 2 - TIME: 2.473439 s