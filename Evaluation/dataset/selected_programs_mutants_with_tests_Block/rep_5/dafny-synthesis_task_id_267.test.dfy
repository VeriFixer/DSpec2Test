
method {:test} Test4() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(5);
expect r0 == 5 * (2 * 5 - 1) * (2 * 5 + 1) / 3;
}

// REPEAT 5 - TIME: 5.4873311 s