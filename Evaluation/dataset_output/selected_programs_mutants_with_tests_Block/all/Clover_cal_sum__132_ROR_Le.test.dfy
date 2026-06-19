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
expect 1797 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(1797);
expect r0 == 1797 * (1797 + 1) / 2;
}

// REPEAT 1 - TIME: 1.693101 s

method {:test} Test1() {
expect 1798 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(1798);
expect r0 == 1798 * (1798 + 1) / 2;
}

// REPEAT 2 - TIME: 2.3081625 s

method {:test} Test2() {
expect 1799 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(1799);
expect r0 == 1799 * (1799 + 1) / 2;
}

// REPEAT 3 - TIME: 3.0064329 s

method {:test} Test3() {
expect 1800 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(1800);
expect r0 == 1800 * (1800 + 1) / 2;
}

// REPEAT 4 - TIME: 3.8625413 s

method {:test} Test4() {
expect 1801 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(1801);
expect r0 == 1801 * (1801 + 1) / 2;
}

// REPEAT 5 - TIME: 4.4564678 s

method {:test} Test5() {
expect 1802 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(1802);
expect r0 == 1802 * (1802 + 1) / 2;
}

// REPEAT 6 - TIME: 5.0303847 s

method {:test} Test6() {
expect 1803 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(1803);
expect r0 == 1803 * (1803 + 1) / 2;
}

// REPEAT 7 - TIME: 5.6751785 s

method {:test} Test7() {
expect 1804 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(1804);
expect r0 == 1804 * (1804 + 1) / 2;
}

// REPEAT 8 - TIME: 6.2541729 s

method {:test} Test8() {
expect 1805 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(1805);
expect r0 == 1805 * (1805 + 1) / 2;
}

// REPEAT 9 - TIME: 6.8587924 s

method {:test} Test9() {
expect 1806 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(1806);
expect r0 == 1806 * (1806 + 1) / 2;
}

// REPEAT 10 - TIME: 7.47198 s
