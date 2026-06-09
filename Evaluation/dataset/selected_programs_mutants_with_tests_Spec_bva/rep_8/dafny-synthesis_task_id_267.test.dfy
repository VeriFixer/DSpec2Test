
method {:test} Test12() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(107);
expect r0 == 107 * (2 * 107 - 1) * (2 * 107 + 1) / 3;
}

// REPEAT 8 - TIME: 10.6742246 s