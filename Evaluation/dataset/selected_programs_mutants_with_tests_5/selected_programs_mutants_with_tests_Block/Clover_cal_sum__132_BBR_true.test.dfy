// Clover_cal_sum.dfy

method {:testEntry} Sum(N: nat) returns (s: nat)
  requires N >= 0
  ensures s == N * (N + 1) / 2
{
  var n := 0;
  s := 0;
  while true
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
method {:test} Test1() {
expect 2439 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(2439);
expect r0 == 2439 * (2439 + 1) / 2;
}
method {:test} Test2() {
expect 10159 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(10159);
expect r0 == 10159 * (10159 + 1) / 2;
}
method {:test} Test3() {
expect 10160 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(10160);
expect r0 == 10160 * (10160 + 1) / 2;
}
method {:test} Test4() {
expect 10161 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(10161);
expect r0 == 10161 * (10161 + 1) / 2;
}
