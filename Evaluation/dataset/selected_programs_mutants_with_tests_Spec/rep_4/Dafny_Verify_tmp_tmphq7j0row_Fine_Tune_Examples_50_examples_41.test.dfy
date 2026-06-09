
method {:test} Test4() {
expect 7722 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5 == 1 || 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7722, 5);
expect 5 + r0 + r1 >= 2 * 7722;
}

// REPEAT 4 - TIME: 6.4720499 s