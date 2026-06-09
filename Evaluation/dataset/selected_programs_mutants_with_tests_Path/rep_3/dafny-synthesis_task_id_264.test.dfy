
method {:test} Test2() {
expect 40 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(40);
expect r0 == 7 * 40;
}

// REPEAT 3 - TIME: 6.5157376 s