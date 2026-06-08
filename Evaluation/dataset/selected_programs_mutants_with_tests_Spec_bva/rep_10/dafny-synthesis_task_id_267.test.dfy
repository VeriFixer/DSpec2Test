
method {:test} Test14() {
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(109);
expect r0 == 109 * (2 * 109 - 1) * (2 * 109 + 1) / 3;
}

// REPEAT 10 - TIME: 12.476651 s