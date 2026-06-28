// dafny-synthesis_task_id_267.dfy

method {:testEntry} SumOfSquaresOfFirstNOddNumbers(n: int) returns (sum: int)
  requires n >= 0
  ensures sum == n * (2 * n - 1) * (2 * n + 1) / 3
{
  sum := 0;
  var i := 1;
  for k := 0 to n
    invariant 0 <= k <= n
    invariant sum == k * (2 * k - 1) * (2 * k + 1) / 3
    invariant i == 2 * k + 1
  {
    sum := sum + i;
    i := i + 2;
  }
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(0);
expect r0 == 0 * (2 * 0 - 1) * (2 * 0 + 1) / 3;
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(100);
expect r0 == 100 * (2 * 100 - 1) * (2 * 100 + 1) / 3;
}

// REPEAT 1 - TIME: 8.2108811 s

method {:test} Test6() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(101);
expect r0 == 101 * (2 * 101 - 1) * (2 * 101 + 1) / 3;
}

// REPEAT 2 - TIME: 9.7422644 s

method {:test} Test7() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(102);
expect r0 == 102 * (2 * 102 - 1) * (2 * 102 + 1) / 3;
}

// REPEAT 3 - TIME: 10.8761341 s

method {:test} Test8() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(103);
expect r0 == 103 * (2 * 103 - 1) * (2 * 103 + 1) / 3;
}

// REPEAT 4 - TIME: 11.7223819 s

method {:test} Test9() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(104);
expect r0 == 104 * (2 * 104 - 1) * (2 * 104 + 1) / 3;
}

// REPEAT 5 - TIME: 12.7508583 s

method {:test} Test10() {
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(105);
expect r0 == 105 * (2 * 105 - 1) * (2 * 105 + 1) / 3;
}

// REPEAT 6 - TIME: 13.5938377 s

method {:test} Test11() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(106);
expect r0 == 106 * (2 * 106 - 1) * (2 * 106 + 1) / 3;
}

// REPEAT 7 - TIME: 14.4040424 s

method {:test} Test12() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(107);
expect r0 == 107 * (2 * 107 - 1) * (2 * 107 + 1) / 3;
}

// REPEAT 8 - TIME: 15.2285209 s

method {:test} Test13() {
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(108);
expect r0 == 108 * (2 * 108 - 1) * (2 * 108 + 1) / 3;
}

// REPEAT 9 - TIME: 16.1449544 s

method {:test} Test14() {
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(109);
expect r0 == 109 * (2 * 109 - 1) * (2 * 109 + 1) / 3;
}

// REPEAT 10 - TIME: 16.9274651 s
