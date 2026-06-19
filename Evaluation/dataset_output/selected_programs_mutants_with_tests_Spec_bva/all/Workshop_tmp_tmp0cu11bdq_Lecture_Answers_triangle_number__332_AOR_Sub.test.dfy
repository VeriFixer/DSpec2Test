// Workshop_tmp_tmp0cu11bdq_Lecture_Answers_triangle_number.dfy

method {:testEntry} TriangleNumber(N: int) returns (t: int)
  requires N >= 0
  ensures t == N * (N + 1) / 2
{
  t := 0;
  var n := 0;
  while n < N
    invariant 0 <= n <= N
    invariant t == n * (n + 1) / 2
    decreases N - n
  {
    n := n - 1;
    t := t + n;
  }
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(0);
expect r0 == 0 * (0 + 1) / 2;
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(100);
expect r0 == 100 * (100 + 1) / 2;
}

// REPEAT 1 - TIME: 5.7899078 s

method {:test} Test6() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(101);
expect r0 == 101 * (101 + 1) / 2;
}

// REPEAT 2 - TIME: 6.7218449 s

method {:test} Test7() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(102);
expect r0 == 102 * (102 + 1) / 2;
}

// REPEAT 3 - TIME: 7.5793478 s

method {:test} Test8() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(103);
expect r0 == 103 * (103 + 1) / 2;
}

// REPEAT 4 - TIME: 8.4095922 s

method {:test} Test9() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(104);
expect r0 == 104 * (104 + 1) / 2;
}

// REPEAT 5 - TIME: 9.3618416 s

method {:test} Test10() {
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(105);
expect r0 == 105 * (105 + 1) / 2;
}

// REPEAT 6 - TIME: 10.2277366 s

method {:test} Test11() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(106);
expect r0 == 106 * (106 + 1) / 2;
}

// REPEAT 7 - TIME: 10.9762067 s

method {:test} Test12() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(107);
expect r0 == 107 * (107 + 1) / 2;
}

// REPEAT 8 - TIME: 11.7398224 s

method {:test} Test13() {
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(108);
expect r0 == 108 * (108 + 1) / 2;
}

// REPEAT 9 - TIME: 12.5039404 s

method {:test} Test14() {
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(109);
expect r0 == 109 * (109 + 1) / 2;
}

// REPEAT 10 - TIME: 13.1987461 s
