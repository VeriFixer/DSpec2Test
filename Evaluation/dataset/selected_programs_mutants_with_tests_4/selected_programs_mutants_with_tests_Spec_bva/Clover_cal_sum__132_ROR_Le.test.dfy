// Clover_cal_sum.dfy

method {:testEntry} Sum(N: nat) returns (s: nat)
  requires N >= 0
  ensures s == N * (N + 1) / 2
{
  var n := 0;
  s := 0;
  while n <= N
    invariant 0 <= n <= N
    invariant s == n * (n + 1) / 2
  {
    n := n + 1;
    s := s + n;
  }
}

method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(0);
expect r0 == 0 * (0 + 1) / 2;
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(100);
expect r0 == 100 * (100 + 1) / 2;
}
method {:test} Test6() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(101);
expect r0 == 101 * (101 + 1) / 2;
}
method {:test} Test7() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(102);
expect r0 == 102 * (102 + 1) / 2;
}
method {:test} Test8() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(103);
expect r0 == 103 * (103 + 1) / 2;
}
