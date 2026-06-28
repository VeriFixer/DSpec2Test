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

method {:test} Test65() {
expect 1 <= 9, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(9);
expect 0 <= r0 < 9;
}
method {:test} Test66() {
var r0 := Min(12, 12);
expect r0 <= 12 && r0 <= 12;
expect r0 == 12 || r0 == 12;
}
method {:test} Test67() {
var r0 := Min(13, 12);
expect r0 <= 13 && r0 <= 12;
expect r0 == 13 || r0 == 12;
}
method {:test} Test68() {
var r0 := Max(39, 38);
}
method {:test} Test69() {
var r0, r1 := MaxSum(7726, 7727);
expect r0 == 7726 + 7727;
expect r1 == if 7726 >= 7727 then 7726 else 7727;
}
method {:test} Test70() {
expect 15454 <= 2 * 7727, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15454, 7727);
expect 15454 == r0 + r1;
expect (7727 == r0 || 7727 == r1) && r0 <= 7727 && r1 <= 7727;
}
method {:test} Test71() {
expect 15453 <= 2 * 7727, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15453, 7727);
expect 15453 == r0 + r1;
expect (7727 == r0 || 7727 == r1) && r0 <= 7727 && r1 <= 7727;
}
method {:test} Test72() {
TestMaxSum(39, 38);
}

// REPEAT 9 - TIME: 33.4337825 s
