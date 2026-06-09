// Clover_cal_sum.dfy

method {:testEntry} Sum(N: int) returns (s: int)
  requires N >= 0
  ensures s == N * (N + 1) / 2
{
  var n := 0;
  s := 0;
  while n != N
    invariant 0 <= n <= N
    invariant s == n * (n + 1) / 2
  {
    s := s + n;
  }
}

method {:test} Test0() {
expect 1797 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(1797);
expect r0 == 1797 * (1797 + 1) / 2;
}

// REPEAT 1 - TIME: 1.790816 s
