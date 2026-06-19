// Clover_cal_sum.dfy

method {:testEntry} Sum(N: int) returns (s: int)
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

// REPEAT 1 - TIME: 5.9174277 s

method {:test} Test6() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(101);
expect r0 == 101 * (101 + 1) / 2;
}

// REPEAT 2 - TIME: 7.0357009 s

method {:test} Test7() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(102);
expect r0 == 102 * (102 + 1) / 2;
}

// REPEAT 3 - TIME: 7.8058155 s

method {:test} Test8() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(103);
expect r0 == 103 * (103 + 1) / 2;
}

// REPEAT 4 - TIME: 8.6212907 s

method {:test} Test9() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(104);
expect r0 == 104 * (104 + 1) / 2;
}

// REPEAT 5 - TIME: 9.4452337 s

method {:test} Test10() {
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(105);
expect r0 == 105 * (105 + 1) / 2;
}

// REPEAT 6 - TIME: 10.2614799 s

method {:test} Test11() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(106);
expect r0 == 106 * (106 + 1) / 2;
}

// REPEAT 7 - TIME: 11.0118261 s

method {:test} Test12() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(107);
expect r0 == 107 * (107 + 1) / 2;
}

// REPEAT 8 - TIME: 11.6818812 s

method {:test} Test13() {
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(108);
expect r0 == 108 * (108 + 1) / 2;
}

// REPEAT 9 - TIME: 12.6208755 s

method {:test} Test14() {
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(109);
expect r0 == 109 * (109 + 1) / 2;
}

// REPEAT 10 - TIME: 13.2874968 s
