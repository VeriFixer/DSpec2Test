// Prog-Fun-Solutions_tmp_tmp7_gmnz5f_mockExam2_p2.dfy

method {:testEntry} problem2(p: int, q: int, X: int, Y: int)
    returns (r: int, s: int)
  requires p == 2 * X + Y && q == X + 3
  ensures r == X && s == Y
{
  assert p == 2 * X + Y && q == X + 3;
  r, s := p, q;
  assert r == 2 * X + Y && s == X + 3;
  r := r + 2 * s + 6;
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

// REPEAT 1 - TIME: 2.6016505 s

method {:test} Test1() {
expect 1239 == 2 * 619 + 1 && 622 == 619 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(1239, 622, 619, 1);
expect r0 == 619 && r1 == 1;
}

// REPEAT 2 - TIME: 3.5573495 s

method {:test} Test2() {
expect 1242 == 2 * 620 + 2 && 623 == 620 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(1242, 623, 620, 2);
expect r0 == 620 && r1 == 2;
}

// REPEAT 3 - TIME: 4.523128 s

method {:test} Test3() {
expect 1245 == 2 * 621 + 3 && 624 == 621 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(1245, 624, 621, 3);
expect r0 == 621 && r1 == 3;
}

// REPEAT 4 - TIME: 5.4858297 s

method {:test} Test4() {
expect 1248 == 2 * 622 + 4 && 625 == 622 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(1248, 625, 622, 4);
expect r0 == 622 && r1 == 4;
}

// REPEAT 5 - TIME: 6.3714805 s

method {:test} Test5() {
expect 1251 == 2 * 623 + 5 && 626 == 623 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(1251, 626, 623, 5);
expect r0 == 623 && r1 == 5;
}

// REPEAT 6 - TIME: 7.3563932 s

method {:test} Test6() {
expect 1254 == 2 * 624 + 6 && 627 == 624 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(1254, 627, 624, 6);
expect r0 == 624 && r1 == 6;
}

// REPEAT 7 - TIME: 8.2693043 s

method {:test} Test7() {
expect 1257 == 2 * 625 + 7 && 628 == 625 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(1257, 628, 625, 7);
expect r0 == 625 && r1 == 7;
}

// REPEAT 8 - TIME: 8.9475752 s

method {:test} Test8() {
expect 1260 == 2 * 626 + 8 && 629 == 626 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(1260, 629, 626, 8);
expect r0 == 626 && r1 == 8;
}

// REPEAT 9 - TIME: 9.741831 s

method {:test} Test9() {
expect 1263 == 2 * 627 + 9 && 630 == 627 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(1263, 630, 627, 9);
expect r0 == 627 && r1 == 9;
}

// REPEAT 10 - TIME: 10.5673867 s
