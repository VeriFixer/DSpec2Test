// dafny-synthesis_task_id_599.dfy

method {:testEntry} SumAndAverage(n: int) returns (sum: int, average: real)
  requires n > 0
  ensures sum == n * (n + 1) / 2
  ensures average == sum as real / n as real
{
  for i := 1 to n + 1
    invariant 0 <= i <= n + 1
    invariant sum == (i - 1) * i / 2
  {
    sum := sum + i;
  }
  sum := 0;
  average := sum as real / n as real;
}

method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(1);
expect r0 == 1 * (1 + 1) / 2;
expect r1 == r0 as real / 1 as real;
}
method {:test} Test2() {
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(100);
expect r0 == 100 * (100 + 1) / 2;
expect r1 == r0 as real / 100 as real;
}
method {:test} Test5() {
expect 199 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(199);
expect r0 == 199 * (199 + 1) / 2;
expect r1 == r0 as real / 199 as real;
}

// REPEAT 1 - TIME: 7.1400059 s
