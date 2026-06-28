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

method {:test} Test57() {
expect 1 <= 8, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(8);
expect 0 <= r0 < 8;
}
method {:test} Test58() {
var r0 := Min(11, 11);
expect r0 <= 11 && r0 <= 11;
expect r0 == 11 || r0 == 11;
}
method {:test} Test59() {
var r0 := Min(11, 10);
expect r0 <= 11 && r0 <= 10;
expect r0 == 11 || r0 == 10;
}
method {:test} Test60() {
var r0 := Max(36, 37);
}
method {:test} Test61() {
var r0, r1 := MaxSum(7725, 7726);
expect r0 == 7725 + 7726;
expect r1 == if 7725 >= 7726 then 7725 else 7726;
}
method {:test} Test62() {
expect 15452 <= 2 * 7726, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15452, 7726);
expect 15452 == r0 + r1;
expect (7726 == r0 || 7726 == r1) && r0 <= 7726 && r1 <= 7726;
}
method {:test} Test63() {
expect 15451 <= 2 * 7726, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15451, 7726);
expect 15451 == r0 + r1;
expect (7726 == r0 || 7726 == r1) && r0 <= 7726 && r1 <= 7726;
}
method {:test} Test64() {
TestMaxSum(37, 36);
}

// REPEAT 8 - TIME: 30.4295117 s
