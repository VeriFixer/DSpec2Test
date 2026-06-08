
method {:test} Test9() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(104);
expect r0 == 104 * (104 + 1) * (104 + 2) / 6;
}

// REPEAT 5 - TIME: 8.3546426 s