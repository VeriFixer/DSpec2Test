
method {:test} Test11() {
expect -98 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(771945, -98);
expect r0 == 771945 / -98;
}

// REPEAT 3 - TIME: 7.7152356 s