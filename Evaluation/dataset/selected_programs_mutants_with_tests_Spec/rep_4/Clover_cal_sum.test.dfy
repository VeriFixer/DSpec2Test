
method {:test} Test3() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(3);
expect r0 == 3 * (3 + 1) / 2;
}

// REPEAT 4 - TIME: 5.1741945 s