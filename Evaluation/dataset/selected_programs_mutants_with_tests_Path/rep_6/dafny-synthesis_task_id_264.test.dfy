
method {:test} Test5() {
expect 43 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(43);
expect r0 == 7 * 43;
}

// REPEAT 6 - TIME: 9.8336422 s