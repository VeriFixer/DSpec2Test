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
    sum := i * i * i * i;
    i := 2;
  }
}


method {:test} Test0() {
expect 21 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(21);
expect r0 == 21 * (2 * 21 + 1) * (24 * 21 * 21 * 21 - 12 * 21 * 21 - 14 * 21 + 7) / 15;
}

// REPEAT 1 - TIME: 3.6926845 s

method {:test} Test1() {
expect 58 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(58);
expect r0 == 58 * (2 * 58 + 1) * (24 * 58 * 58 * 58 - 12 * 58 * 58 - 14 * 58 + 7) / 15;
}

// REPEAT 2 - TIME: 5.6214349 s
