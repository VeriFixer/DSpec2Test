
method {:test} Test7() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(102);
expect r0 == 102 * (2 * 102 - 1) * (2 * 102 + 1) / 3;
}

// REPEAT 3 - TIME: 7.4760366 s