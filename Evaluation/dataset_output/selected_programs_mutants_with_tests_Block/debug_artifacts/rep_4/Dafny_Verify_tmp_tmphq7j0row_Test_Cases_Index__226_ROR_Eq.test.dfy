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

method {:test} Test28() {
expect 1 <= 2478, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(2478);
expect 0 <= r0 < 2478;
}
method {:test} Test29() {
var r0 := Min(4, 5);
expect r0 <= 4 && r0 <= 5;
expect r0 == 4 || r0 == 5;
}
method {:test} Test30() {
var r0 := Min(4, 4);
expect r0 <= 4 && r0 <= 4;
expect r0 == 4 || r0 == 4;
}
method {:test} Test31() {
var r0 := Max(4, 5);
}
method {:test} Test32() {
var r0 := Max(4, 4);
}
method {:test} Test33() {
var r0, r1 := MaxSum(4, 5);
expect r0 == 4 + 5;
expect r1 == if 4 >= 5 then 4 else 5;
}
method {:test} Test34() {
var r0, r1 := MaxSum(4, 4);
expect r0 == 4 + 4;
expect r1 == if 4 >= 4 then 4 else 4;
}
method {:test} Test35() {
expect 41 <= 2 * 41, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(41, 41);
expect 41 == r0 + r1;
expect (41 == r0 || 41 == r1) && r0 <= 41 && r1 <= 41;
}
method {:test} Test36() {
TestMaxSum(8857, 8858);
}

// REPEAT 4 - TIME: 14.4963276 s
