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

method {:test} Test64() {
expect 1 <= 2486, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(2486);
expect 0 <= r0 < 2486;
}
method {:test} Test65() {
var r0 := Min(10, 11);
expect r0 <= 10 && r0 <= 11;
expect r0 == 10 || r0 == 11;
}
method {:test} Test66() {
var r0 := Min(10, 10);
expect r0 <= 10 && r0 <= 10;
expect r0 == 10 || r0 == 10;
}
method {:test} Test67() {
var r0 := Max(10, 11);
}
method {:test} Test68() {
var r0 := Max(10, 10);
}
method {:test} Test69() {
var r0, r1 := MaxSum(10, 11);
expect r0 == 10 + 11;
expect r1 == if 10 >= 11 then 10 else 11;
}
method {:test} Test70() {
var r0, r1 := MaxSum(10, 10);
expect r0 == 10 + 10;
expect r1 == if 10 >= 10 then 10 else 10;
}
method {:test} Test71() {
expect 45 <= 2 * 45, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(45, 45);
expect 45 == r0 + r1;
expect (45 == r0 || 45 == r1) && r0 <= 45 && r1 <= 45;
}
method {:test} Test72() {
TestMaxSum(8861, 8862);
}

// REPEAT 8 - TIME: 24.6576939 s
