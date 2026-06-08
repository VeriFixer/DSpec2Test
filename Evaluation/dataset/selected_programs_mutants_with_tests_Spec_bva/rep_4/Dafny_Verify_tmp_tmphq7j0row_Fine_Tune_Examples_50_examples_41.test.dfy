
method {:test} Test26() {
expect 7722 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 103 == 1 || 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7722, 103);
expect 103 + r0 + r1 >= 2 * 7722;
}

// REPEAT 4 - TIME: 11.5405599 s