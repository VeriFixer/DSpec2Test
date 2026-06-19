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
    break;
    n := n + 1;
    t := t + n;
  }
}


method {:test} Test0() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(1);
expect r0 == 1 * (1 + 1) / 2;
}

// REPEAT 1 - TIME: 1.87165 s

method {:test} Test1() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(2);
expect r0 == 2 * (2 + 1) / 2;
}

// REPEAT 2 - TIME: 2.574461 s

method {:test} Test2() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(3);
expect r0 == 3 * (3 + 1) / 2;
}

// REPEAT 3 - TIME: 3.1705119 s

method {:test} Test3() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(4);
expect r0 == 4 * (4 + 1) / 2;
}

// REPEAT 4 - TIME: 3.8399566 s

method {:test} Test4() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(5);
expect r0 == 5 * (5 + 1) / 2;
}

// REPEAT 5 - TIME: 4.4841955 s

method {:test} Test5() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(6);
expect r0 == 6 * (6 + 1) / 2;
}

// REPEAT 6 - TIME: 5.1022073 s

method {:test} Test6() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(7);
expect r0 == 7 * (7 + 1) / 2;
}

// REPEAT 7 - TIME: 5.6850601 s

method {:test} Test7() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(8);
expect r0 == 8 * (8 + 1) / 2;
}

// REPEAT 8 - TIME: 6.2544068 s

method {:test} Test8() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(9);
expect r0 == 9 * (9 + 1) / 2;
}

// REPEAT 9 - TIME: 6.6858205 s

method {:test} Test9() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(10);
expect r0 == 10 * (10 + 1) / 2;
}

// REPEAT 10 - TIME: 7.1807809 s
