
method {:test} Test8() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(103);
expect r0 == 103 * (2 * 103 - 1) * (2 * 103 + 1) / 3;
}

// REPEAT 4 - TIME: 8.0446291 s