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
    sum := sum + (i + i);
    i := i + 2;
  }
}

method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(0);
expect r0 == 0 * (2 * 0 - 1) * (2 * 0 + 1) / 3;
}

// REPEAT 1 - TIME: 2.8592719 s
