
method {:test} Test9() {
expect 14 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(14);
expect r0 == 14 * (2 * 14 - 1) * (2 * 14 + 1) / 3;
}

// REPEAT 10 - TIME: 39.9872752 s