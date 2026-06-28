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
    sum := i * i;
    i := 2;
  }
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(0);
expect r0 == 0 * (2 * 0 - 1) * (2 * 0 + 1) / 3;
}

// REPEAT 1 - TIME: 4.05402 s

method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(1);
expect r0 == 1 * (2 * 1 - 1) * (2 * 1 + 1) / 3;
}

// REPEAT 2 - TIME: 6.9109788 s

method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(2);
expect r0 == 2 * (2 * 2 - 1) * (2 * 2 + 1) / 3;
}

// REPEAT 3 - TIME: 9.2619658 s

method {:test} Test3() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(9);
expect r0 == 9 * (2 * 9 - 1) * (2 * 9 + 1) / 3;
}

// REPEAT 4 - TIME: 11.8821262 s

method {:test} Test4() {
expect 12 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(12);
expect r0 == 12 * (2 * 12 - 1) * (2 * 12 + 1) / 3;
}

// REPEAT 5 - TIME: 14.5541352 s

method {:test} Test5() {
expect 13 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(13);
expect r0 == 13 * (2 * 13 - 1) * (2 * 13 + 1) / 3;
}

// REPEAT 6 - TIME: 16.7538871 s

method {:test} Test6() {
expect 18 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(18);
expect r0 == 18 * (2 * 18 - 1) * (2 * 18 + 1) / 3;
}

// REPEAT 7 - TIME: 18.6999682 s

method {:test} Test7() {
expect 21 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(21);
expect r0 == 21 * (2 * 21 - 1) * (2 * 21 + 1) / 3;
}

// REPEAT 8 - TIME: 21.0188865 s

method {:test} Test8() {
expect 22 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(22);
expect r0 == 22 * (2 * 22 - 1) * (2 * 22 + 1) / 3;
}

// REPEAT 9 - TIME: 23.6020526 s

method {:test} Test9() {
expect 23 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(23);
expect r0 == 23 * (2 * 23 - 1) * (2 * 23 + 1) / 3;
}

// REPEAT 10 - TIME: 26.4378204 s
