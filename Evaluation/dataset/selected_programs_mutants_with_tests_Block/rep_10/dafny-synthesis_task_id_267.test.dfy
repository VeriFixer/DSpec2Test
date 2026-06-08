
method {:test} Test9() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(10);
expect r0 == 10 * (2 * 10 - 1) * (2 * 10 + 1) / 3;
}

// REPEAT 10 - TIME: 9.3131917 s