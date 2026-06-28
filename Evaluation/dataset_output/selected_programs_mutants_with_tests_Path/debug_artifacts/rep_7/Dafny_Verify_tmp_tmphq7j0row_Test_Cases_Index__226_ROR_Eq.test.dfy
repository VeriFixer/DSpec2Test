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
  if x == y {
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

method {:test} Test61() {
expect 1 <= 2484, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(2484);
expect 0 <= r0 < 2484;
}
method {:test} Test62() {
var r0 := Min(9, 9);
expect r0 <= 9 && r0 <= 9;
expect r0 == 9 || r0 == 9;
}
method {:test} Test63() {
var r0 := Min(8, 9);
expect r0 <= 8 && r0 <= 9;
expect r0 == 8 || r0 == 9;
}
method {:test} Test64() {
var r0 := Max(9, 9);
}
method {:test} Test65() {
var r0 := Max(8, 9);
}
method {:test} Test66() {
var r0, r1 := MaxSum(9, 9);
expect r0 == 9 + 9;
expect r1 == if 9 >= 9 then 9 else 9;
}
method {:test} Test67() {
var r0, r1 := MaxSum(8, 9);
expect r0 == 8 + 9;
expect r1 == if 8 >= 9 then 8 else 9;
}
method {:test} Test68() {
expect 44 <= 2 * 44, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(44, 44);
expect 44 == r0 + r1;
expect (44 == r0 || 44 == r1) && r0 <= 44 && r1 <= 44;
}
method {:test} Test69() {
TestMaxSum(8860, 8861);
}

// REPEAT 7 - TIME: 121.0701737 s
