
method {:test} Test8() {
expect 13 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(13);
expect r0 == 13 * (2 * 13 - 1) * (2 * 13 + 1) / 3;
}

// REPEAT 9 - TIME: 35.732152 s