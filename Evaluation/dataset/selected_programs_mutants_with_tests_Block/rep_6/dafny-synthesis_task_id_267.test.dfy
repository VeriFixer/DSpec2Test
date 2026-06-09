
method {:test} Test5() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(6);
expect r0 == 6 * (2 * 6 - 1) * (2 * 6 + 1) / 3;
}

// REPEAT 6 - TIME: 6.1520574 s