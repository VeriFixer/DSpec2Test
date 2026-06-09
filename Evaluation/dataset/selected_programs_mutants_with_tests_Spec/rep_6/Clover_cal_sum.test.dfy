
method {:test} Test5() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(5);
expect r0 == 5 * (5 + 1) / 2;
}

// REPEAT 6 - TIME: 6.5584575 s