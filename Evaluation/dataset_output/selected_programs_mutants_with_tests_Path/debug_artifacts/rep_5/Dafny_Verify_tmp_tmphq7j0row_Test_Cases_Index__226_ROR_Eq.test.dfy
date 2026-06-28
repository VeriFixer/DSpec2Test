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

method {:test} Test41() {
expect 1 <= 2480, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(2480);
expect 0 <= r0 < 2480;
}
method {:test} Test42() {
var r0 := Min(6, 6);
expect r0 <= 6 && r0 <= 6;
expect r0 == 6 || r0 == 6;
}
method {:test} Test43() {
var r0 := Min(5, 6);
expect r0 <= 5 && r0 <= 6;
expect r0 == 5 || r0 == 6;
}
method {:test} Test44() {
var r0 := Max(6, 6);
}
method {:test} Test45() {
var r0 := Max(5, 6);
}
method {:test} Test46() {
var r0, r1 := MaxSum(6, 6);
expect r0 == 6 + 6;
expect r1 == if 6 >= 6 then 6 else 6;
}
method {:test} Test47() {
var r0, r1 := MaxSum(5, 6);
expect r0 == 5 + 6;
expect r1 == if 5 >= 6 then 5 else 6;
}
method {:test} Test48() {
expect 42 <= 2 * 42, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(42, 42);
expect 42 == r0 + r1;
expect (42 == r0 || 42 == r1) && r0 <= 42 && r1 <= 42;
}
method {:test} Test49() {
TestMaxSum(8858, 8859);
}

// REPEAT 5 - TIME: 80.1953478 s
