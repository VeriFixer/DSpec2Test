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

// REPEAT 1 - TIME: 7.6293871 s

method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(1);
expect r0 == 1 * (2 * 1 - 1) * (2 * 1 + 1) / 3;
}

// REPEAT 2 - TIME: 11.2838942 s

method {:test} Test2() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(3);
expect r0 == 3 * (2 * 3 - 1) * (2 * 3 + 1) / 3;
}

// REPEAT 3 - TIME: 14.6580834 s

method {:test} Test3() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(6);
expect r0 == 6 * (2 * 6 - 1) * (2 * 6 + 1) / 3;
}

// REPEAT 4 - TIME: 17.7987206 s

method {:test} Test4() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(7);
expect r0 == 7 * (2 * 7 - 1) * (2 * 7 + 1) / 3;
}

// REPEAT 5 - TIME: 23.1271931 s

method {:test} Test5() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(8);
expect r0 == 8 * (2 * 8 - 1) * (2 * 8 + 1) / 3;
}

// REPEAT 6 - TIME: 27.9427588 s

method {:test} Test6() {
expect 11 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(11);
expect r0 == 11 * (2 * 11 - 1) * (2 * 11 + 1) / 3;
}

// REPEAT 7 - TIME: 32.014769 s

method {:test} Test7() {
expect 12 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(12);
expect r0 == 12 * (2 * 12 - 1) * (2 * 12 + 1) / 3;
}

// REPEAT 8 - TIME: 36.6355588 s

method {:test} Test8() {
expect 13 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(13);
expect r0 == 13 * (2 * 13 - 1) * (2 * 13 + 1) / 3;
}

// REPEAT 9 - TIME: 41.1915525 s

method {:test} Test9() {
expect 14 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(14);
expect r0 == 14 * (2 * 14 - 1) * (2 * 14 + 1) / 3;
}

// REPEAT 10 - TIME: 45.8198022 s
