
method {:test} Test3() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(4);
expect r0 == 4 * (2 * 4 - 1) * (2 * 4 + 1) / 3;
}

// REPEAT 4 - TIME: 4.7573153 s