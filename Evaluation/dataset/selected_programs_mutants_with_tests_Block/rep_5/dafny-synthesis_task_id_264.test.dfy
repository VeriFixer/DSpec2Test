
method {:test} Test4() {
expect 42 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(42);
expect r0 == 7 * 42;
}

// REPEAT 5 - TIME: 5.0835053 s