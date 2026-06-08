
method {:test} Test14() {
expect -95 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(772064, -95);
expect r0 == 772064 / -95;
}

// REPEAT 6 - TIME: 10.3803651 s