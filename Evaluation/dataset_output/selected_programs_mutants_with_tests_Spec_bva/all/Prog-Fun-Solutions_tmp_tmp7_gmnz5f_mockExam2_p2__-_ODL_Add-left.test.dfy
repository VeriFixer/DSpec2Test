// Prog-Fun-Solutions_tmp_tmp7_gmnz5f_mockExam2_p2.dfy

method {:testEntry} problem2(p: int, q: int, X: int, Y: int)
    returns (r: int, s: int)
  requires p == 2 * X + Y && q == X + 3
  ensures r == X && s == Y
{
  assert p == 2 * X + Y && q == X + 3;
  r, s := p, q;
  assert r == 2 * X + Y && s == X + 3;
  r := 6;
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

// REPEAT 1 - TIME: 12.3687505 s

method {:test} Test15() {
expect 1445 == 2 * 619 + 207 && 622 == 619 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(1445, 622, 619, 207);
expect r0 == 619 && r1 == 207;
}

// REPEAT 2 - TIME: 13.105265 s

method {:test} Test16() {
expect 1448 == 2 * 620 + 208 && 623 == 620 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(1448, 623, 620, 208);
expect r0 == 620 && r1 == 208;
}

// REPEAT 3 - TIME: 13.9867664 s

method {:test} Test17() {
expect 1451 == 2 * 621 + 209 && 624 == 621 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(1451, 624, 621, 209);
expect r0 == 621 && r1 == 209;
}

// REPEAT 4 - TIME: 14.9014109 s

method {:test} Test18() {
expect 1454 == 2 * 622 + 210 && 625 == 622 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(1454, 625, 622, 210);
expect r0 == 622 && r1 == 210;
}

// REPEAT 5 - TIME: 15.7042258 s

method {:test} Test19() {
expect 1457 == 2 * 623 + 211 && 626 == 623 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(1457, 626, 623, 211);
expect r0 == 623 && r1 == 211;
}

// REPEAT 6 - TIME: 16.7484577 s

method {:test} Test20() {
expect 1460 == 2 * 624 + 212 && 627 == 624 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(1460, 627, 624, 212);
expect r0 == 624 && r1 == 212;
}

// REPEAT 7 - TIME: 17.6072073 s

method {:test} Test21() {
expect 1463 == 2 * 625 + 213 && 628 == 625 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(1463, 628, 625, 213);
expect r0 == 625 && r1 == 213;
}

// REPEAT 8 - TIME: 18.4192211 s

method {:test} Test22() {
expect 1466 == 2 * 626 + 214 && 629 == 626 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(1466, 629, 626, 214);
expect r0 == 626 && r1 == 214;
}

// REPEAT 9 - TIME: 19.4111446 s

method {:test} Test23() {
expect 1469 == 2 * 627 + 215 && 630 == 627 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(1469, 630, 627, 215);
expect r0 == 627 && r1 == 215;
}

// REPEAT 10 - TIME: 20.3301269 s
