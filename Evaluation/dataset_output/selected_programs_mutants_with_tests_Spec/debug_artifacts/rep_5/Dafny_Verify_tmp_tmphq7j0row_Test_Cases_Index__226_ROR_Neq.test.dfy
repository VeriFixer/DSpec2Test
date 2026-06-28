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

method {:test} Test33() {
expect 1 <= 5, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(5);
expect 0 <= r0 < 5;
}
method {:test} Test34() {
var r0 := Min(6, 6);
expect r0 <= 6 && r0 <= 6;
expect r0 == 6 || r0 == 6;
}
method {:test} Test35() {
var r0 := Min(7, 6);
expect r0 <= 7 && r0 <= 6;
expect r0 == 7 || r0 == 6;
}
method {:test} Test36() {
var r0 := Max(31, 30);
}
method {:test} Test37() {
var r0, r1 := MaxSum(7722, 7723);
expect r0 == 7722 + 7723;
expect r1 == if 7722 >= 7723 then 7722 else 7723;
}
method {:test} Test38() {
expect 15446 <= 2 * 7723, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15446, 7723);
expect 15446 == r0 + r1;
expect (7723 == r0 || 7723 == r1) && r0 <= 7723 && r1 <= 7723;
}
method {:test} Test39() {
expect 15445 <= 2 * 7723, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15445, 7723);
expect 15445 == r0 + r1;
expect (7723 == r0 || 7723 == r1) && r0 <= 7723 && r1 <= 7723;
}
method {:test} Test40() {
TestMaxSum(31, 30);
}

// REPEAT 5 - TIME: 20.7342375 s
