
method {:test} Test8() {
expect 1805 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(1805);
expect r0 == 1805 * (1805 + 1) / 2;
}

// REPEAT 9 - TIME: 6.9281435 s