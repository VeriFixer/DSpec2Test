
method {:test} Test7() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(102);
expect r0 == 4 * 102 * 102 - 3 * 102;
}

// REPEAT 3 - TIME: 7.2555039 s