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
    n := n - 1;
    s := s + n;
  }
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(0);
expect r0 == 0 * (0 + 1) / 2;
}

// REPEAT 1 - TIME: 2.6971485 s

method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(1);
expect r0 == 1 * (1 + 1) / 2;
}

// REPEAT 2 - TIME: 3.5445457 s

method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(2);
expect r0 == 2 * (2 + 1) / 2;
}

// REPEAT 3 - TIME: 4.5513847 s

method {:test} Test3() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(3);
expect r0 == 3 * (3 + 1) / 2;
}

// REPEAT 4 - TIME: 5.6021917 s

method {:test} Test4() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(4);
expect r0 == 4 * (4 + 1) / 2;
}

// REPEAT 5 - TIME: 6.6716592 s

method {:test} Test5() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(5);
expect r0 == 5 * (5 + 1) / 2;
}

// REPEAT 6 - TIME: 7.5198607 s

method {:test} Test6() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(6);
expect r0 == 6 * (6 + 1) / 2;
}

// REPEAT 7 - TIME: 8.4817678 s

method {:test} Test7() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(7);
expect r0 == 7 * (7 + 1) / 2;
}

// REPEAT 8 - TIME: 9.2703235 s

method {:test} Test8() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(8);
expect r0 == 8 * (8 + 1) / 2;
}

// REPEAT 9 - TIME: 10.104634 s

method {:test} Test9() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(9);
expect r0 == 9 * (9 + 1) / 2;
}

// REPEAT 10 - TIME: 10.936343 s
