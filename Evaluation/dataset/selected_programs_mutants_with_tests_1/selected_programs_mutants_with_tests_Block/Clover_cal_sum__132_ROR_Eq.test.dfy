// Clover_cal_sum.dfy

method {:testEntry} Sum(N: nat) returns (s: nat)
  requires N >= 0
  ensures s == N * (N + 1) / 2
{
  var n := 0;
  s := 0;
  while n == N
    invariant 0 <= n <= N
    invariant s == n * (n + 1) / 2
  {
    n := n + 1;
    s := s + n;
  }
}

method {:test} Test0() {
expect 2438 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(2438);
expect r0 == 2438 * (2438 + 1) / 2;
}
