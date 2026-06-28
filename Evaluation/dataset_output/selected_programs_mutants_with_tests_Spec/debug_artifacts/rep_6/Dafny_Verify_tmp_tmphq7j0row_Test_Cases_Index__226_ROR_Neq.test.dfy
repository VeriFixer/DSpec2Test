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

method {:test} Test41() {
expect 1 <= 6, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(6);
expect 0 <= r0 < 6;
}
method {:test} Test42() {
var r0 := Min(8, 8);
expect r0 <= 8 && r0 <= 8;
expect r0 == 8 || r0 == 8;
}
method {:test} Test43() {
var r0 := Min(8, 7);
expect r0 <= 8 && r0 <= 7;
expect r0 == 8 || r0 == 7;
}
method {:test} Test44() {
var r0 := Max(32, 33);
}
method {:test} Test45() {
var r0, r1 := MaxSum(7723, 7724);
expect r0 == 7723 + 7724;
expect r1 == if 7723 >= 7724 then 7723 else 7724;
}
method {:test} Test46() {
expect 15448 <= 2 * 7724, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15448, 7724);
expect 15448 == r0 + r1;
expect (7724 == r0 || 7724 == r1) && r0 <= 7724 && r1 <= 7724;
}
method {:test} Test47() {
expect 15447 <= 2 * 7724, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15447, 7724);
expect 15447 == r0 + r1;
expect (7724 == r0 || 7724 == r1) && r0 <= 7724 && r1 <= 7724;
}
method {:test} Test48() {
TestMaxSum(33, 32);
}

// REPEAT 6 - TIME: 24.2166908 s
