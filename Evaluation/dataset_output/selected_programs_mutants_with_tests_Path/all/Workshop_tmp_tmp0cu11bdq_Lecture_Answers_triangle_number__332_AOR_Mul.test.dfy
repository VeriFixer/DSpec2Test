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
    n := n * 1;
    t := t + n;
  }
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(0);
expect r0 == 0 * (0 + 1) / 2;
}

// REPEAT 1 - TIME: 4.5035425 s

method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(1);
expect r0 == 1 * (1 + 1) / 2;
}

// REPEAT 2 - TIME: 7.5049806 s

method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(2);
expect r0 == 2 * (2 + 1) / 2;
}

// REPEAT 3 - TIME: 10.0338228 s

method {:test} Test3() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(3);
expect r0 == 3 * (3 + 1) / 2;
}

// REPEAT 4 - TIME: 12.4161992 s

method {:test} Test4() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(4);
expect r0 == 4 * (4 + 1) / 2;
}

// REPEAT 5 - TIME: 15.2391564 s

method {:test} Test5() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(5);
expect r0 == 5 * (5 + 1) / 2;
}

// REPEAT 6 - TIME: 18.069333 s

method {:test} Test6() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(6);
expect r0 == 6 * (6 + 1) / 2;
}

// REPEAT 7 - TIME: 20.6393682 s

method {:test} Test7() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(7);
expect r0 == 7 * (7 + 1) / 2;
}

// REPEAT 8 - TIME: 22.9567552 s

method {:test} Test8() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(8);
expect r0 == 8 * (8 + 1) / 2;
}

// REPEAT 9 - TIME: 25.6398674 s

method {:test} Test9() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(9);
expect r0 == 9 * (9 + 1) / 2;
}

// REPEAT 10 - TIME: 28.0935448 s
