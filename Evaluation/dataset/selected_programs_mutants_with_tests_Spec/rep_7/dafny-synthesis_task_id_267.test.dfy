
method {:test} Test6() {
expect 18 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(18);
expect r0 == 18 * (2 * 18 - 1) * (2 * 18 + 1) / 3;
}

// REPEAT 7 - TIME: 7.2975263 s