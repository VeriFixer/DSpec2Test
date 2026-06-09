
method {:test} Test17() {
expect -92 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(772247, -92);
expect r0 == 772247 / -92;
}

// REPEAT 9 - TIME: 11.6921735 s