
method {:test} Test1() {
expect 1798 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(1798);
expect r0 == 1798 * (1798 + 1) / 2;
}

// REPEAT 2 - TIME: 2.4614628 s