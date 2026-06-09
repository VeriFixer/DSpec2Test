
method {:test} Test3() {
expect 7723 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(7723, 7723);
expect r1 * 7723 + r0 == 7723 && 0 <= r0 < 7723 && 0 <= r1;
}

// REPEAT 4 - TIME: 3.8703472 s