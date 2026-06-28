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

method {:test} Test9() {
expect 1 <= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(2);
expect 0 <= r0 < 2;
}
method {:test} Test10() {
var r0 := Min(2, 2);
expect r0 <= 2 && r0 <= 2;
expect r0 == 2 || r0 == 2;
}
method {:test} Test11() {
var r0 := Min(2, 1);
expect r0 <= 2 && r0 <= 1;
expect r0 == 2 || r0 == 1;
}
method {:test} Test12() {
var r0 := Max(25, 24);
}
method {:test} Test13() {
var r0, r1 := MaxSum(7719, 7720);
expect r0 == 7719 + 7720;
expect r1 == if 7719 >= 7720 then 7719 else 7720;
}
method {:test} Test14() {
expect 15440 <= 2 * 7720, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15440, 7720);
expect 15440 == r0 + r1;
expect (7720 == r0 || 7720 == r1) && r0 <= 7720 && r1 <= 7720;
}
method {:test} Test15() {
expect 15439 <= 2 * 7720, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15439, 7720);
expect 15439 == r0 + r1;
expect (7720 == r0 || 7720 == r1) && r0 <= 7720 && r1 <= 7720;
}
method {:test} Test16() {
TestMaxSum(25, 24);
}

// REPEAT 2 - TIME: 10.3395738 s
