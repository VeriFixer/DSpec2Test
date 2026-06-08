
method {:test} Test8() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(9);
expect r0 == 9 * (2 * 9 - 1) * (2 * 9 + 1) / 3;
}

// REPEAT 9 - TIME: 8.5680005 s