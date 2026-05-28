// Clover_cal_sum.dfy

method {:testEntry} Sum(N: nat) returns (s: nat)
  requires N >= 0
  ensures s == N * (N + 1) / 2
{
  var n := 0;
  s := 0;
  while n != N
    invariant 0 <= n <= N
    invariant s == n * (n + 1) / 2
  {
    break;
    n := n + 1;
    s := s + n;
  }
}

method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(0);
expect r0 == 0 * (0 + 1) / 2;
}
method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(1);
expect r0 == 1 * (1 + 1) / 2;
}
method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(2);
expect r0 == 2 * (2 + 1) / 2;
}
method {:test} Test3() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(3);
expect r0 == 3 * (3 + 1) / 2;
}
method {:test} Test4() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(4);
expect r0 == 4 * (4 + 1) / 2;
}
method {:test} Test5() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(5);
expect r0 == 5 * (5 + 1) / 2;
}
