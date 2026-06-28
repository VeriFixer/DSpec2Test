// Dafny_Verify_tmp_tmphq7j0row_Test_Cases_Index.dfy

method {:testEntry} Index(n: int) returns (i: int)
  requires 1 <= n
  ensures 0 <= i < n
{
  i := 2;
}

method {:testEntry} Min(x: int, y: int) returns (m: int)
  ensures m <= x && m <= y
  ensures m == x || m == y
{
  if x >= y {
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

method {:test} Test0() {
expect 1 <= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(1);
expect 0 <= r0 < 1;
}
method {:test} Test1() {
var r0 := Min(-1, 0);
expect r0 <= -1 && r0 <= 0;
expect r0 == -1 || r0 == 0;
}
method {:test} Test2() {
var r0 := Min(0, 0);
expect r0 <= 0 && r0 <= 0;
expect r0 == 0 || r0 == 0;
}
method {:test} Test3() {
var r0 := Max(0, -1);
}
method {:test} Test4() {
var r0 := Max(-1, 0);
}
method {:test} Test5() {
var r0, r1 := MaxSum(-1, 0);
expect r0 == -1 + 0;
expect r1 == if -1 >= 0 then -1 else 0;
}
method {:test} Test6() {
var r0, r1 := MaxSum(0, 0);
expect r0 == 0 + 0;
expect r1 == if 0 >= 0 then 0 else 0;
}
method {:test} Test7() {
MaxSumCaller();
}
method {:test} Test8() {
expect 38 <= 2 * 38, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(38, 38);
expect 38 == r0 + r1;
expect (38 == r0 || 38 == r1) && r0 <= 38 && r1 <= 38;
}
method {:test} Test9() {
TestMaxSum(8854, 8855);
}

// REPEAT 1 - TIME: 5.2256515 s
