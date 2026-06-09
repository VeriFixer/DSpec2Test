
method {:test} Test6() {
expect 1803 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(1803);
expect r0 == 1803 * (1803 + 1) / 2;
}

// REPEAT 7 - TIME: 5.8080538 s