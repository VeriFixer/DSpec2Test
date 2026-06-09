
method {:test} Test6() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(101);
expect r0 == 101 * (2 * 101 - 1) * (2 * 101 + 1) / 3;
}

// REPEAT 2 - TIME: 6.6922649 s