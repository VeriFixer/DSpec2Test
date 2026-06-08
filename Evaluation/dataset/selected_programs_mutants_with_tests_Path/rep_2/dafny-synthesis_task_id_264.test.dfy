
method {:test} Test1() {
expect 39 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(39);
expect r0 == 7 * 39;
}

// REPEAT 2 - TIME: 3.9503964 s