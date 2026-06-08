
method {:test} Test13() {
expect -96 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(772031, -96);
expect r0 == 772031 / -96;
}

// REPEAT 5 - TIME: 9.5325381 s