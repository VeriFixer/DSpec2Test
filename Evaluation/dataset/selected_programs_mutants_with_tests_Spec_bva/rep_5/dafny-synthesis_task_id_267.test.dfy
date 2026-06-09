
method {:test} Test9() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(104);
expect r0 == 104 * (2 * 104 - 1) * (2 * 104 + 1) / 3;
}

// REPEAT 5 - TIME: 8.7305938 s