
method {:test} Test4() {
expect 16 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(16);
expect r0 == 16 * (2 * 16 - 1) * (2 * 16 + 1) / 3;
}

// REPEAT 5 - TIME: 6.9761696 s