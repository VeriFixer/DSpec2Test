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

method {:test} Test0() {
expect 1 <= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(1);
expect 0 <= r0 < 1;
}
method {:test} Test1() {
var r0 := Min(0, 0);
expect r0 <= 0 && r0 <= 0;
expect r0 == 0 || r0 == 0;
}
method {:test} Test2() {
var r0 := Min(1, 0);
expect r0 <= 1 && r0 <= 0;
expect r0 == 1 || r0 == 0;
}
method {:test} Test3() {
var r0 := Max(0, 0);
}
method {:test} Test4() {
var r0, r1 := MaxSum(7718, 7719);
expect r0 == 7718 + 7719;
expect r1 == if 7718 >= 7719 then 7718 else 7719;
}
method {:test} Test5() {
MaxSumCaller();
}
method {:test} Test6() {
expect 7719 <= 2 * 7719, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(7719, 7719);
expect 7719 == r0 + r1;
expect (7719 == r0 || 7719 == r1) && r0 <= 7719 && r1 <= 7719;
}
method {:test} Test7() {
expect 4873 <= 2 * 2437, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(4873, 2437);
expect 4873 == r0 + r1;
expect (2437 == r0 || 2437 == r1) && r0 <= 2437 && r1 <= 2437;
}
method {:test} Test8() {
TestMaxSum(0, 0);
}

// REPEAT 1 - TIME: 7.0654536 s
