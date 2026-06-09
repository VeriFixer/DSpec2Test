
method {:test} Test6() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(101);
expect r0 == 7 * 101;
}

// REPEAT 2 - TIME: 5.634892 s