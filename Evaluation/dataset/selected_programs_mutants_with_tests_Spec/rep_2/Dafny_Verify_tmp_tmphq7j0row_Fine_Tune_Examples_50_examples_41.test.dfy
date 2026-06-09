
method {:test} Test2() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 3 == 1 || 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(1, 3);
expect 3 + r0 + r1 >= 2 * 1;
}

// REPEAT 2 - TIME: 4.2452633 s