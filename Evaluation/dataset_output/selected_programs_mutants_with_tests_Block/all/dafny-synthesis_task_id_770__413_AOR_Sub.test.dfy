// dafny-synthesis_task_id_770.dfy

method {:testEntry} SumOfFourthPowerOfOddNumbers(n: int) returns (sum: int)
  requires n > 0
  ensures sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15
{
  sum := 0;
  var i := 1;
  for k := 0 to n
    invariant 0 <= k <= n
    invariant i == 2 * k + 1
    invariant sum == k * (2 * k + 1) * (24 * k * k * k - 12 * k * k - 14 * k + 7) / 15
  {
    sum := sum - i * i * i * i;
    i := i + 2;
  }
}


method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(1);
expect r0 == 1 * (2 * 1 + 1) * (24 * 1 * 1 * 1 - 12 * 1 * 1 - 14 * 1 + 7) / 15;
}

// REPEAT 1 - TIME: 2.3721506 s

method {:test} Test1() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(2);
expect r0 == 2 * (2 * 2 + 1) * (24 * 2 * 2 * 2 - 12 * 2 * 2 - 14 * 2 + 7) / 15;
}

// REPEAT 2 - TIME: 3.2155292 s

method {:test} Test2() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(3);
expect r0 == 3 * (2 * 3 + 1) * (24 * 3 * 3 * 3 - 12 * 3 * 3 - 14 * 3 + 7) / 15;
}

// REPEAT 3 - TIME: 3.9779622 s

method {:test} Test3() {
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(4);
expect r0 == 4 * (2 * 4 + 1) * (24 * 4 * 4 * 4 - 12 * 4 * 4 - 14 * 4 + 7) / 15;
}

// REPEAT 4 - TIME: 4.8023373 s

method {:test} Test4() {
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(5);
expect r0 == 5 * (2 * 5 + 1) * (24 * 5 * 5 * 5 - 12 * 5 * 5 - 14 * 5 + 7) / 15;
}

// REPEAT 5 - TIME: 5.6542952 s

method {:test} Test5() {
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(6);
expect r0 == 6 * (2 * 6 + 1) * (24 * 6 * 6 * 6 - 12 * 6 * 6 - 14 * 6 + 7) / 15;
}

// REPEAT 6 - TIME: 6.5281387 s

method {:test} Test6() {
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(7);
expect r0 == 7 * (2 * 7 + 1) * (24 * 7 * 7 * 7 - 12 * 7 * 7 - 14 * 7 + 7) / 15;
}

// REPEAT 7 - TIME: 7.3219486 s

method {:test} Test7() {
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(8);
expect r0 == 8 * (2 * 8 + 1) * (24 * 8 * 8 * 8 - 12 * 8 * 8 - 14 * 8 + 7) / 15;
}

// REPEAT 8 - TIME: 7.9952577 s

method {:test} Test8() {
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(9);
expect r0 == 9 * (2 * 9 + 1) * (24 * 9 * 9 * 9 - 12 * 9 * 9 - 14 * 9 + 7) / 15;
}

// REPEAT 9 - TIME: 8.6298454 s

method {:test} Test9() {
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(10);
expect r0 == 10 * (2 * 10 + 1) * (24 * 10 * 10 * 10 - 12 * 10 * 10 - 14 * 10 + 7) / 15;
}

// REPEAT 10 - TIME: 9.2401342 s
