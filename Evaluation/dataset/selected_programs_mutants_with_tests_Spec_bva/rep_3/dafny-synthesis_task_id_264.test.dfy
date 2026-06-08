
method {:test} Test7() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(102);
expect r0 == 7 * 102;
}

// REPEAT 3 - TIME: 7.2343721 s