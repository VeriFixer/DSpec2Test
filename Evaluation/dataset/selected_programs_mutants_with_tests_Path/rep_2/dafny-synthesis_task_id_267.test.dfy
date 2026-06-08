
method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(1);
expect r0 == 1 * (2 * 1 - 1) * (2 * 1 + 1) / 3;
}

// REPEAT 2 - TIME: 9.4310352 s