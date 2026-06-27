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

method {:test} Test49() {
expect 1 <= 7, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(7);
expect 0 <= r0 < 7;
}
method {:test} Test50() {
var r0 := Min(9, 9);
expect r0 <= 9 && r0 <= 9;
expect r0 == 9 || r0 == 9;
}
method {:test} Test51() {
var r0 := Min(10, 9);
expect r0 <= 10 && r0 <= 9;
expect r0 == 10 || r0 == 9;
}
method {:test} Test52() {
var r0 := Max(34, 35);
}
method {:test} Test53() {
var r0, r1 := MaxSum(7724, 7725);
expect r0 == 7724 + 7725;
expect r1 == if 7724 >= 7725 then 7724 else 7725;
}
method {:test} Test54() {
expect 15450 <= 2 * 7725, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15450, 7725);
expect 15450 == r0 + r1;
expect (7725 == r0 || 7725 == r1) && r0 <= 7725 && r1 <= 7725;
}
method {:test} Test55() {
expect 15449 <= 2 * 7725, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15449, 7725);
expect 15449 == r0 + r1;
expect (7725 == r0 || 7725 == r1) && r0 <= 7725 && r1 <= 7725;
}
method {:test} Test56() {
TestMaxSum(35, 34);
}

// REPEAT 7 - TIME: 25.7575246 s
