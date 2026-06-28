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

method {:test} Test11() {
expect 1 <= 2474, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(2474);
expect 0 <= r0 < 2474;
}
method {:test} Test12() {
var r0 := Min(1, 1);
expect r0 <= 1 && r0 <= 1;
expect r0 == 1 || r0 == 1;
}
method {:test} Test13() {
var r0 := Min(1, 2);
expect r0 <= 1 && r0 <= 2;
expect r0 == 1 || r0 == 2;
}
method {:test} Test14() {
var r0 := Max(1, 1);
}
method {:test} Test15() {
var r0 := Max(1, 2);
}
method {:test} Test16() {
var r0, r1 := MaxSum(1, 1);
expect r0 == 1 + 1;
expect r1 == if 1 >= 1 then 1 else 1;
}
method {:test} Test17() {
var r0, r1 := MaxSum(1, 2);
expect r0 == 1 + 2;
expect r1 == if 1 >= 2 then 1 else 2;
}
method {:test} Test18() {
expect 39 <= 2 * 39, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(39, 39);
expect 39 == r0 + r1;
expect (39 == r0 || 39 == r1) && r0 <= 39 && r1 <= 39;
}
method {:test} Test19() {
TestMaxSum(8855, 8856);
}

// REPEAT 2 - TIME: 31.1823512 s
