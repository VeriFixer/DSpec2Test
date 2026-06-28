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

method {:test} Test25() {
expect 1 <= 4, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(4);
expect 0 <= r0 < 4;
}
method {:test} Test26() {
var r0 := Min(5, 5);
expect r0 <= 5 && r0 <= 5;
expect r0 == 5 || r0 == 5;
}
method {:test} Test27() {
var r0 := Min(5, 4);
expect r0 <= 5 && r0 <= 4;
expect r0 == 5 || r0 == 4;
}
method {:test} Test28() {
var r0 := Max(29, 28);
}
method {:test} Test29() {
var r0, r1 := MaxSum(7721, 7722);
expect r0 == 7721 + 7722;
expect r1 == if 7721 >= 7722 then 7721 else 7722;
}
method {:test} Test30() {
expect 15444 <= 2 * 7722, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15444, 7722);
expect 15444 == r0 + r1;
expect (7722 == r0 || 7722 == r1) && r0 <= 7722 && r1 <= 7722;
}
method {:test} Test31() {
expect 15443 <= 2 * 7722, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15443, 7722);
expect 15443 == r0 + r1;
expect (7722 == r0 || 7722 == r1) && r0 <= 7722 && r1 <= 7722;
}
method {:test} Test32() {
TestMaxSum(29, 28);
}

// REPEAT 4 - TIME: 17.2603734 s
