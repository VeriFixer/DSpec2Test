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
expect 4868 == 2 * 2434 + 0 && 2437 == 2434 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(4868, 2437, 2434, 0);
expect r0 == 2434 && r1 == 0;
}

// REPEAT 1 - TIME: 23.4073667 s
