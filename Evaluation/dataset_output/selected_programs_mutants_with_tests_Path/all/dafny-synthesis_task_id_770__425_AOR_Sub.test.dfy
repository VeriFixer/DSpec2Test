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
    sum := sum + (i * i * i - i);
    i := i + 2;
  }
}


method {:test} Test0() {
expect 21 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(21);
expect r0 == 21 * (2 * 21 + 1) * (24 * 21 * 21 * 21 - 12 * 21 * 21 - 14 * 21 + 7) / 15;
}

// REPEAT 1 - TIME: 5.5864417 s

method {:test} Test1() {
expect 27 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(27);
expect r0 == 27 * (2 * 27 + 1) * (24 * 27 * 27 * 27 - 12 * 27 * 27 - 14 * 27 + 7) / 15;
}

// REPEAT 2 - TIME: 7.9482383 s

method {:test} Test2() {
expect 28 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(28);
expect r0 == 28 * (2 * 28 + 1) * (24 * 28 * 28 * 28 - 12 * 28 * 28 - 14 * 28 + 7) / 15;
}

// REPEAT 3 - TIME: 10.2817103 s

method {:test} Test3() {
expect 30 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(30);
expect r0 == 30 * (2 * 30 + 1) * (24 * 30 * 30 * 30 - 12 * 30 * 30 - 14 * 30 + 7) / 15;
}

// REPEAT 4 - TIME: 14.2791683 s

method {:test} Test4() {
expect 31 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(31);
expect r0 == 31 * (2 * 31 + 1) * (24 * 31 * 31 * 31 - 12 * 31 * 31 - 14 * 31 + 7) / 15;
}

// REPEAT 5 - TIME: 17.1157654 s

method {:test} Test5() {
expect 32 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(32);
expect r0 == 32 * (2 * 32 + 1) * (24 * 32 * 32 * 32 - 12 * 32 * 32 - 14 * 32 + 7) / 15;
}

// REPEAT 6 - TIME: 19.5270184 s

method {:test} Test6() {
expect 33 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(33);
expect r0 == 33 * (2 * 33 + 1) * (24 * 33 * 33 * 33 - 12 * 33 * 33 - 14 * 33 + 7) / 15;
}

// REPEAT 7 - TIME: 21.626437 s

method {:test} Test7() {
expect 34 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(34);
expect r0 == 34 * (2 * 34 + 1) * (24 * 34 * 34 * 34 - 12 * 34 * 34 - 14 * 34 + 7) / 15;
}

// REPEAT 8 - TIME: 24.253625 s

method {:test} Test8() {
expect 35 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(35);
expect r0 == 35 * (2 * 35 + 1) * (24 * 35 * 35 * 35 - 12 * 35 * 35 - 14 * 35 + 7) / 15;
}

// REPEAT 9 - TIME: 27.234642 s
