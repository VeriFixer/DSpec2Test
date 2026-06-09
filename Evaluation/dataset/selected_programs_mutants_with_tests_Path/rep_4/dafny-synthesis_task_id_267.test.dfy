
method {:test} Test3() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(6);
expect r0 == 6 * (2 * 6 - 1) * (2 * 6 + 1) / 3;
}

// REPEAT 4 - TIME: 15.3280039 s