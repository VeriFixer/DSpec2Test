// Prog-Fun-Solutions_tmp_tmp7_gmnz5f_mockExam2_p2.dfy

method {:testEntry} problem2(p: int, q: int, X: int, Y: int)
    returns (r: int, s: int)
  requires p == 2 * X + Y && q == X + 3
  ensures r == X && s == Y
{
  assert p == 2 * X + Y && q == X + 3;
  r, s := p, q;
  assert r == 2 * X + Y && s == X + 3;
  r := r - 2 * s;
  assert r == 2 * X + Y - 2 * X - 6 + 6 && s == X + 3;
  assert r == Y && s == X + 3;
  s := s - 3;
  assert r == Y && s == X;
  r, s := s, r;
  assert s == Y && r == X;
}

method {:test} Test0() {
expect 1236 == 2 * 618 + 0 && 621 == 618 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(1236, 621, 618, 0);
expect r0 == 618 && r1 == 0;
}
method {:test} Test1() {
expect 0 == 2 * -103 + 206 && -100 == -103 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(0, -100, -103, 206);
expect r0 == -103 && r1 == 206;
}
method {:test} Test2() {
expect 0 == 2 * 97 + -194 && 100 == 97 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(0, 100, 97, -194);
expect r0 == 97 && r1 == -194;
}
method {:test} Test3() {
expect 0 == 2 * -100 + 200 && -97 == -100 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(0, -97, -100, 200);
expect r0 == -100 && r1 == 200;
}
method {:test} Test4() {
expect 0 == 2 * 100 + -200 && 103 == 100 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(0, 103, 100, -200);
expect r0 == 100 && r1 == -200;
}
method {:test} Test5() {
expect 1136 == 2 * 618 + -100 && 621 == 618 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(1136, 621, 618, -100);
expect r0 == 618 && r1 == -100;
}
method {:test} Test6() {
expect 1336 == 2 * 618 + 100 && 621 == 618 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(1336, 621, 618, 100);
expect r0 == 618 && r1 == 100;
}

// REPEAT 1 - TIME: 8.7899676 s
