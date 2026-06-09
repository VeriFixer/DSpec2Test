
method {:test} Test14() {
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(109);
expect r0 == 7 * 109;
}

// REPEAT 10 - TIME: 11.5784646 s