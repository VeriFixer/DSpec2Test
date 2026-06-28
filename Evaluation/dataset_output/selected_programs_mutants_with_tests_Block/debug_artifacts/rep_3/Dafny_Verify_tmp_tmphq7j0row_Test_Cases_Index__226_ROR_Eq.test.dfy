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

method {:test} Test19() {
expect 1 <= 2476, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(2476);
expect 0 <= r0 < 2476;
}
method {:test} Test20() {
var r0 := Min(3, 3);
expect r0 <= 3 && r0 <= 3;
expect r0 == 3 || r0 == 3;
}
method {:test} Test21() {
var r0 := Min(2, 3);
expect r0 <= 2 && r0 <= 3;
expect r0 == 2 || r0 == 3;
}
method {:test} Test22() {
var r0 := Max(2, 3);
}
method {:test} Test23() {
var r0 := Max(3, 3);
}
method {:test} Test24() {
var r0, r1 := MaxSum(2, 3);
expect r0 == 2 + 3;
expect r1 == if 2 >= 3 then 2 else 3;
}
method {:test} Test25() {
var r0, r1 := MaxSum(3, 3);
expect r0 == 3 + 3;
expect r1 == if 3 >= 3 then 3 else 3;
}
method {:test} Test26() {
expect 40 <= 2 * 40, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(40, 40);
expect 40 == r0 + r1;
expect (40 == r0 || 40 == r1) && r0 <= 40 && r1 <= 40;
}
method {:test} Test27() {
TestMaxSum(8856, 8857);
}

// REPEAT 3 - TIME: 10.9865491 s
