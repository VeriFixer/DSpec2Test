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

method {:test} Test91() {
expect 1 <= 2490, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(2490);
expect 0 <= r0 < 2490;
}
method {:test} Test92() {
var r0 := Min(13, 13);
expect r0 <= 13 && r0 <= 13;
expect r0 == 13 || r0 == 13;
}
method {:test} Test93() {
var r0 := Min(13, 14);
expect r0 <= 13 && r0 <= 14;
expect r0 == 13 || r0 == 14;
}
method {:test} Test94() {
var r0 := Max(13, 13);
}
method {:test} Test95() {
var r0 := Max(13, 14);
}
method {:test} Test96() {
var r0, r1 := MaxSum(13, 13);
expect r0 == 13 + 13;
expect r1 == if 13 >= 13 then 13 else 13;
}
method {:test} Test97() {
var r0, r1 := MaxSum(13, 14);
expect r0 == 13 + 14;
expect r1 == if 13 >= 14 then 13 else 14;
}
method {:test} Test98() {
expect 47 <= 2 * 47, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(47, 47);
expect 47 == r0 + r1;
expect (47 == r0 || 47 == r1) && r0 <= 47 && r1 <= 47;
}
method {:test} Test99() {
TestMaxSum(8863, 8864);
}

// REPEAT 10 - TIME: 146.2326889 s
