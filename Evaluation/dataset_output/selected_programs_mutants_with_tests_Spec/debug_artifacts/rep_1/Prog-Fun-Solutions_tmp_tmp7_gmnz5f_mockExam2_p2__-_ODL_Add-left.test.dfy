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

// REPEAT 1 - TIME: 2.888101 s
