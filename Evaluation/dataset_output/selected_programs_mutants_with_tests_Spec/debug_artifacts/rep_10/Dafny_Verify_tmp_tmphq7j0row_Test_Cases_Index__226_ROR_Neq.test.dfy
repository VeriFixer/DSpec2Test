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

method {:test} Test73() {
expect 1 <= 10, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(10);
expect 0 <= r0 < 10;
}
method {:test} Test74() {
var r0 := Min(14, 14);
expect r0 <= 14 && r0 <= 14;
expect r0 == 14 || r0 == 14;
}
method {:test} Test75() {
var r0 := Min(14, 13);
expect r0 <= 14 && r0 <= 13;
expect r0 == 14 || r0 == 13;
}
method {:test} Test76() {
var r0 := Max(40, 41);
}
method {:test} Test77() {
var r0, r1 := MaxSum(7727, 7728);
expect r0 == 7727 + 7728;
expect r1 == if 7727 >= 7728 then 7727 else 7728;
}
method {:test} Test78() {
expect 15455 <= 2 * 7728, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15455, 7728);
expect 15455 == r0 + r1;
expect (7728 == r0 || 7728 == r1) && r0 <= 7728 && r1 <= 7728;
}
method {:test} Test80() {
TestMaxSum(41, 40);
}

// REPEAT 10 - TIME: 33.126585 s
