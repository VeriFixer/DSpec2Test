
method {:test} Test8() {
expect 20 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(20);
expect r0 == 20 * (2 * 20 - 1) * (2 * 20 + 1) / 3;
}

// REPEAT 9 - TIME: 8.435941 s