
method {:test} Test9() {
expect 21 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(21);
expect r0 == 21 * (2 * 21 - 1) * (2 * 21 + 1) / 3;
}

// REPEAT 10 - TIME: 10.6061398 s