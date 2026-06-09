
method {:test} Test6() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(101);
expect r0 == 6 * 101 * (101 - 1) + 1;
}

// REPEAT 2 - TIME: 5.2704288 s