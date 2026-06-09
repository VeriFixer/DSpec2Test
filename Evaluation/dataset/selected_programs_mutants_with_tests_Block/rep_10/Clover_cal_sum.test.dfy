
method {:test} Test9() {
expect 1806 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(1806);
expect r0 == 1806 * (1806 + 1) / 2;
}

// REPEAT 10 - TIME: 7.5661116 s