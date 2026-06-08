
method {:test} Test9() {
expect 11 > 0 && 2483 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(11, 2483);
expect r0 == (11 + 2483) / 2;
}

// REPEAT 10 - TIME: 13.0593589 s