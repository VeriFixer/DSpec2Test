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

method {:test} Test73() {
expect 1 <= 2488, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(2488);
expect 0 <= r0 < 2488;
}
method {:test} Test74() {
var r0 := Min(11, 12);
expect r0 <= 11 && r0 <= 12;
expect r0 == 11 || r0 == 12;
}
method {:test} Test75() {
var r0 := Min(12, 12);
expect r0 <= 12 && r0 <= 12;
expect r0 == 12 || r0 == 12;
}
method {:test} Test76() {
var r0 := Max(12, 12);
}
method {:test} Test77() {
var r0 := Max(11, 12);
}
method {:test} Test78() {
var r0, r1 := MaxSum(11, 12);
expect r0 == 11 + 12;
expect r1 == if 11 >= 12 then 11 else 12;
}
method {:test} Test79() {
var r0, r1 := MaxSum(12, 12);
expect r0 == 12 + 12;
expect r1 == if 12 >= 12 then 12 else 12;
}
method {:test} Test80() {
expect 46 <= 2 * 46, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(46, 46);
expect 46 == r0 + r1;
expect (46 == r0 || 46 == r1) && r0 <= 46 && r1 <= 46;
}
method {:test} Test81() {
TestMaxSum(8862, 8863);
}

// REPEAT 9 - TIME: 27.8059117 s
