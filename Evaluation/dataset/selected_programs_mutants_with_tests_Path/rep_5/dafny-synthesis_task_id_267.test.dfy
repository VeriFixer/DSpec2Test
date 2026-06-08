
method {:test} Test4() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(7);
expect r0 == 7 * (2 * 7 - 1) * (2 * 7 + 1) / 3;
}

// REPEAT 5 - TIME: 17.3455105 s