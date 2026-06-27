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

method {:test} Test51() {
expect 1 <= 2482, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(2482);
expect 0 <= r0 < 2482;
}
method {:test} Test52() {
var r0 := Min(7, 7);
expect r0 <= 7 && r0 <= 7;
expect r0 == 7 || r0 == 7;
}
method {:test} Test53() {
var r0 := Min(7, 8);
expect r0 <= 7 && r0 <= 8;
expect r0 == 7 || r0 == 8;
}
method {:test} Test54() {
var r0 := Max(7, 7);
}
method {:test} Test55() {
var r0 := Max(7, 8);
}
method {:test} Test56() {
var r0, r1 := MaxSum(7, 7);
expect r0 == 7 + 7;
expect r1 == if 7 >= 7 then 7 else 7;
}
method {:test} Test57() {
var r0, r1 := MaxSum(7, 8);
expect r0 == 7 + 8;
expect r1 == if 7 >= 8 then 7 else 8;
}
method {:test} Test58() {
expect 43 <= 2 * 43, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(43, 43);
expect 43 == r0 + r1;
expect (43 == r0 || 43 == r1) && r0 <= 43 && r1 <= 43;
}
method {:test} Test59() {
TestMaxSum(8859, 8860);
}

// REPEAT 6 - TIME: 76.354465 s
