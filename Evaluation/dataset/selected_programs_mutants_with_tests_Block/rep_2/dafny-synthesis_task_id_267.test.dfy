
method {:test} Test1() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(2);
expect r0 == 2 * (2 * 2 - 1) * (2 * 2 + 1) / 3;
}

// REPEAT 2 - TIME: 3.2245072 s