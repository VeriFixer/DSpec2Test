
method {:test} Test15() {
expect -94 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(772115, -94);
expect r0 == 772115 / -94;
}

// REPEAT 7 - TIME: 11.2152202 s