
method {:test} Test9() {
expect 7727 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 10 == 1 || 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7727, 10);
expect 10 + r0 + r1 >= 2 * 7727;
}

// REPEAT 9 - TIME: 7.117308 s