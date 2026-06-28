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
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(1);
expect r0 == 1 * (2 * 1 - 1) * (2 * 1 + 1) / 3;
}

// REPEAT 1 - TIME: 2.2188579 s

method {:test} Test1() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(2);
expect r0 == 2 * (2 * 2 - 1) * (2 * 2 + 1) / 3;
}

// REPEAT 2 - TIME: 3.0039012 s

method {:test} Test2() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(3);
expect r0 == 3 * (2 * 3 - 1) * (2 * 3 + 1) / 3;
}

// REPEAT 3 - TIME: 3.785401 s

method {:test} Test3() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(4);
expect r0 == 4 * (2 * 4 - 1) * (2 * 4 + 1) / 3;
}

// REPEAT 4 - TIME: 4.7559303 s

method {:test} Test4() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(5);
expect r0 == 5 * (2 * 5 - 1) * (2 * 5 + 1) / 3;
}

// REPEAT 5 - TIME: 5.6457592 s

method {:test} Test5() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(6);
expect r0 == 6 * (2 * 6 - 1) * (2 * 6 + 1) / 3;
}

// REPEAT 6 - TIME: 6.2891463 s

method {:test} Test6() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(7);
expect r0 == 7 * (2 * 7 - 1) * (2 * 7 + 1) / 3;
}

// REPEAT 7 - TIME: 7.1605795 s

method {:test} Test7() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(8);
expect r0 == 8 * (2 * 8 - 1) * (2 * 8 + 1) / 3;
}

// REPEAT 8 - TIME: 7.8804953 s

method {:test} Test8() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(9);
expect r0 == 9 * (2 * 9 - 1) * (2 * 9 + 1) / 3;
}

// REPEAT 9 - TIME: 8.541788 s

method {:test} Test9() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(10);
expect r0 == 10 * (2 * 10 - 1) * (2 * 10 + 1) / 3;
}

// REPEAT 10 - TIME: 9.2133655 s
