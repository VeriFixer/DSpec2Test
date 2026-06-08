
method {:test} Test8() {
expect 46 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(46);
expect r0 == 7 * 46;
}

// REPEAT 9 - TIME: 9.768525 s