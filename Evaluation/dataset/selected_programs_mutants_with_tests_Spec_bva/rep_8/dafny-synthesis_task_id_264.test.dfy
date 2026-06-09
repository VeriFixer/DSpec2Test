
method {:test} Test12() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(107);
expect r0 == 7 * 107;
}

// REPEAT 8 - TIME: 10.3387938 s