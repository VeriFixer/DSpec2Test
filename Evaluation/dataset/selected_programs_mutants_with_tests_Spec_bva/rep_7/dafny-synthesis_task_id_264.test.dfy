
method {:test} Test11() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(106);
expect r0 == 7 * 106;
}

// REPEAT 7 - TIME: 10.3726724 s