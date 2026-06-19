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
    i := i + 2;
  }
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(0);
expect r0 == 0 * (2 * 0 - 1) * (2 * 0 + 1) / 3;
}

// REPEAT 1 - TIME: 2.5016642 s

method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(1);
expect r0 == 1 * (2 * 1 - 1) * (2 * 1 + 1) / 3;
}

// REPEAT 2 - TIME: 3.329358 s

method {:test} Test2() {
expect 14 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(14);
expect r0 == 14 * (2 * 14 - 1) * (2 * 14 + 1) / 3;
}

// REPEAT 3 - TIME: 4.514167 s

method {:test} Test3() {
expect 15 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(15);
expect r0 == 15 * (2 * 15 - 1) * (2 * 15 + 1) / 3;
}

// REPEAT 4 - TIME: 5.5496116 s

method {:test} Test4() {
expect 16 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(16);
expect r0 == 16 * (2 * 16 - 1) * (2 * 16 + 1) / 3;
}

// REPEAT 5 - TIME: 6.5333733 s

method {:test} Test5() {
expect 17 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(17);
expect r0 == 17 * (2 * 17 - 1) * (2 * 17 + 1) / 3;
}

// REPEAT 6 - TIME: 7.4254225 s

method {:test} Test6() {
expect 18 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(18);
expect r0 == 18 * (2 * 18 - 1) * (2 * 18 + 1) / 3;
}

// REPEAT 7 - TIME: 8.1497939 s

method {:test} Test7() {
expect 19 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(19);
expect r0 == 19 * (2 * 19 - 1) * (2 * 19 + 1) / 3;
}

// REPEAT 8 - TIME: 8.7750487 s

method {:test} Test8() {
expect 20 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(20);
expect r0 == 20 * (2 * 20 - 1) * (2 * 20 + 1) / 3;
}

// REPEAT 9 - TIME: 9.5162775 s

method {:test} Test9() {
expect 21 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(21);
expect r0 == 21 * (2 * 21 - 1) * (2 * 21 + 1) / 3;
}

// REPEAT 10 - TIME: 10.0652219 s
