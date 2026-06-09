
method {:test} Test6() {
expect -7 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(0, -7);
expect r0 == 0 / -7;
}

// REPEAT 7 - TIME: 6.4135367 s