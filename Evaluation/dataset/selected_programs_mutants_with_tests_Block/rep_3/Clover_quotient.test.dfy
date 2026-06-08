
method {:test} Test2() {
expect 7722 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(7722, 7722);
expect r1 * 7722 + r0 == 7722 && 0 <= r0 < 7722 && 0 <= r1;
}

// REPEAT 3 - TIME: 3.185171 s