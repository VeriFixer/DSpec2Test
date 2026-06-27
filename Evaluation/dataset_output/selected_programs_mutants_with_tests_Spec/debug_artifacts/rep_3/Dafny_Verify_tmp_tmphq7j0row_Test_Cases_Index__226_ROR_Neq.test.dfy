// Dafny_Verify_tmp_tmphq7j0row_Test_Cases_Index.dfy

method {:testEntry} Index(n: int) returns (i: int)
  requires 1 <= n
  ensures 0 <= i < n
{
  i := n / 2;
}

method {:testEntry} Min(x: int, y: int) returns (m: int)
  ensures m <= x && m <= y
  ensures m == x || m == y
{
  if x != y {
    m := y;
  } else {
    m := x;
  }
  assert m <= x && m <= y;
}

method {:testEntry} Max(x: int, y: int) returns (m: int)
{
  if x >= y {
    m := x;
  } else {
    m := y;
  }
  assert m >= x && m >= y;
}

method {:testEntry} MaxSum(x: int, y: int)
    returns (s: int, m: int)
  ensures s == x + y
  ensures m == if x >= y then x else y
{
  s := x + y;
  if x >= y {
    m := x;
  } else {
    m := y;
  }
}

method {:testEntry} MaxSumCaller()
{
  var x: int := 1928;
  var y: int := 1;
  var a, b: int;
  a, b := MaxSum(x, y);
  assert a == 1929;
  assert b == 1928;
}

method {:testEntry} ReconstructFromMaxSum(s: int, m: int)
    returns (x: int, y: int)
  requires s <= 2 * m
  ensures s == x + y
  ensures (m == x || m == y) && x <= m && y <= m
{
  x := m;
  y := s - m;
}

method {:testEntry} TestMaxSum(x: int, y: int)
{
  var s, m := MaxSum(x, y);
  var xx, yy := ReconstructFromMaxSum(s, m);
  assert (xx == x && yy == y) || (xx == y && yy == x);
}

method {:test} Test17() {
expect 1 <= 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(3);
expect 0 <= r0 < 3;
}
method {:test} Test18() {
var r0 := Min(3, 3);
expect r0 <= 3 && r0 <= 3;
expect r0 == 3 || r0 == 3;
}
method {:test} Test19() {
var r0 := Min(4, 3);
expect r0 <= 4 && r0 <= 3;
expect r0 == 4 || r0 == 3;
}
method {:test} Test20() {
var r0 := Max(27, 26);
}
method {:test} Test21() {
var r0, r1 := MaxSum(7720, 7721);
expect r0 == 7720 + 7721;
expect r1 == if 7720 >= 7721 then 7720 else 7721;
}
method {:test} Test22() {
expect 15442 <= 2 * 7721, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15442, 7721);
expect 15442 == r0 + r1;
expect (7721 == r0 || 7721 == r1) && r0 <= 7721 && r1 <= 7721;
}
method {:test} Test23() {
expect 15441 <= 2 * 7721, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15441, 7721);
expect 15441 == r0 + r1;
expect (7721 == r0 || 7721 == r1) && r0 <= 7721 && r1 <= 7721;
}
method {:test} Test24() {
TestMaxSum(27, 26);
}

// REPEAT 3 - TIME: 14.1611192 s
