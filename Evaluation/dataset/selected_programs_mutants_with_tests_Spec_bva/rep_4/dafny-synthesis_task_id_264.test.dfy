
method {:test} Test8() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(103);
expect r0 == 7 * 103;
}

// REPEAT 4 - TIME: 7.3996372 s