
method {:test} Test3() {
expect 41 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(41);
expect r0 == 7 * 41;
}

// REPEAT 4 - TIME: 4.669458 s