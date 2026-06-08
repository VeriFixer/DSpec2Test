
method {:test} Test2() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(3);
expect r0 == 3 * (2 * 3 - 1) * (2 * 3 + 1) / 3;
}

// REPEAT 3 - TIME: 12.4000604 s