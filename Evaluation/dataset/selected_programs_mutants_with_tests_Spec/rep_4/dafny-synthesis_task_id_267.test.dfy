
method {:test} Test3() {
expect 15 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(15);
expect r0 == 15 * (2 * 15 - 1) * (2 * 15 + 1) / 3;
}

// REPEAT 4 - TIME: 5.857496 s