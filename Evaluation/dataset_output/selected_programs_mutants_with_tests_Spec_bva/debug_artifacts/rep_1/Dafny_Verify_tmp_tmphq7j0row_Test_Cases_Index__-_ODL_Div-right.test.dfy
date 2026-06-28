// Dafny_Verify_tmp_tmphq7j0row_Test_Cases_Index.dfy

method {:testEntry} Index(n: int) returns (i: int)
  requires 1 <= n
  ensures 0 <= i < n
{
  i := n;
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
method {:test} Test2() {
expect 1 <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(100);
expect 0 <= r0 < 100;
}
method {:test} Test5() {
expect 1 <= 101, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(101);
expect 0 <= r0 < 101;
}
method {:test} Test8() {
var r0 := Min(0, 0);
expect r0 <= 0 && r0 <= 0;
expect r0 == 0 || r0 == 0;
}
method {:test} Test9() {
var r0 := Min(-100, 0);
expect r0 <= -100 && r0 <= 0;
expect r0 == -100 || r0 == 0;
}
method {:test} Test10() {
var r0 := Min(100, 100);
expect r0 <= 100 && r0 <= 100;
expect r0 == 100 || r0 == 100;
}
method {:test} Test11() {
var r0 := Min(-100, -100);
expect r0 <= -100 && r0 <= -100;
expect r0 == -100 || r0 == -100;
}
method {:test} Test12() {
var r0 := Min(0, 100);
expect r0 <= 0 && r0 <= 100;
expect r0 == 0 || r0 == 100;
}
method {:test} Test18() {
var r0 := Min(1, 0);
expect r0 <= 1 && r0 <= 0;
expect r0 == 1 || r0 == 0;
}
method {:test} Test19() {
var r0 := Min(-100, -101);
expect r0 <= -100 && r0 <= -101;
expect r0 == -100 || r0 == -101;
}
method {:test} Test20() {
var r0 := Min(100, 0);
expect r0 <= 100 && r0 <= 0;
expect r0 == 100 || r0 == 0;
}
method {:test} Test21() {
var r0 := Min(0, -100);
expect r0 <= 0 && r0 <= -100;
expect r0 == 0 || r0 == -100;
}
method {:test} Test22() {
var r0 := Min(101, 100);
expect r0 <= 101 && r0 <= 100;
expect r0 == 101 || r0 == 100;
}
method {:test} Test28() {
var r0 := Max(0, 0);
}
method {:test} Test29() {
var r0 := Max(-100, 0);
}
method {:test} Test30() {
var r0 := Max(100, 0);
}
method {:test} Test31() {
var r0 := Max(0, -100);
}
method {:test} Test32() {
var r0 := Max(0, 100);
}
method {:test} Test38() {
var r0, r1 := MaxSum(7718, 7719);
expect r0 == 7718 + 7719;
expect r1 == if 7718 >= 7719 then 7718 else 7719;
}
method {:test} Test39() {
var r0, r1 := MaxSum(-100, 7620);
expect r0 == -100 + 7620;
expect r1 == if -100 >= 7620 then -100 else 7620;
}
method {:test} Test40() {
var r0, r1 := MaxSum(100, 101);
expect r0 == 100 + 101;
expect r1 == if 100 >= 101 then 100 else 101;
}
method {:test} Test41() {
var r0, r1 := MaxSum(-101, -100);
expect r0 == -101 + -100;
expect r1 == if -101 >= -100 then -101 else -100;
}
method {:test} Test42() {
var r0, r1 := MaxSum(0, 100);
expect r0 == 0 + 100;
expect r1 == if 0 >= 100 then 0 else 100;
}
method {:test} Test44() {
var r0, r1 := MaxSum(-7770, 7670);
expect r0 == -7770 + 7670;
expect r1 == if -7770 >= 7670 then -7770 else 7670;
}
method {:test} Test45() {
var r0, r1 := MaxSum(49, 51);
expect r0 == 49 + 51;
expect r1 == if 49 >= 51 then 49 else 51;
}
method {:test} Test48() {
var r0, r1 := MaxSum(99, 100);
expect r0 == 99 + 100;
expect r1 == if 99 >= 100 then 99 else 100;
}
method {:test} Test51() {
MaxSumCaller();
}
method {:test} Test54() {
expect 7719 <= 2 * 7719, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(7719, 7719);
expect 7719 == r0 + r1;
expect (7719 == r0 || 7719 == r1) && r0 <= 7719 && r1 <= 7719;
}
method {:test} Test55() {
expect -100 <= 2 * 1186, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(-100, 1186);
expect -100 == r0 + r1;
expect (1186 == r0 || 1186 == r1) && r0 <= 1186 && r1 <= 1186;
}
method {:test} Test56() {
expect 2 <= 2 * 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(2, 1);
expect 2 == r0 + r1;
expect (1 == r0 || 1 == r1) && r0 <= 1 && r1 <= 1;
}
method {:test} Test57() {
expect -200 <= 2 * -100, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(-200, -100);
expect -200 == r0 + r1;
expect (-100 == r0 || -100 == r1) && r0 <= -100 && r1 <= -100;
}
method {:test} Test58() {
expect 0 <= 2 * 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(0, 100);
expect 0 == r0 + r1;
expect (100 == r0 || 100 == r1) && r0 <= 100 && r1 <= 100;
}
method {:test} Test64() {
expect 200 <= 2 * 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(200, 100);
expect 200 == r0 + r1;
expect (100 == r0 || 100 == r1) && r0 <= 100 && r1 <= 100;
}
method {:test} Test67() {
expect 4873 <= 2 * 2437, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(4873, 2437);
expect 4873 == r0 + r1;
expect (2437 == r0 || 2437 == r1) && r0 <= 2437 && r1 <= 2437;
}
method {:test} Test68() {
expect -100 <= 2 * -49, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(-100, -49);
expect -100 == r0 + r1;
expect (-49 == r0 || -49 == r1) && r0 <= -49 && r1 <= -49;
}
method {:test} Test69() {
expect 2 <= 2 * 1238, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(2, 1238);
expect 2 == r0 + r1;
expect (1238 == r0 || 1238 == r1) && r0 <= 1238 && r1 <= 1238;
}
method {:test} Test70() {
expect -201 <= 2 * -100, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(-201, -100);
expect -201 == r0 + r1;
expect (-100 == r0 || -100 == r1) && r0 <= -100 && r1 <= -100;
}
method {:test} Test74() {
expect 201 <= 2 * 101, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(201, 101);
expect 201 == r0 + r1;
expect (101 == r0 || 101 == r1) && r0 <= 101 && r1 <= 101;
}
method {:test} Test80() {
TestMaxSum(0, 0);
}
method {:test} Test81() {
TestMaxSum(-100, 0);
}
method {:test} Test82() {
TestMaxSum(100, 0);
}
method {:test} Test83() {
TestMaxSum(0, -100);
}
method {:test} Test84() {
TestMaxSum(0, 100);
}

// REPEAT 1 - TIME: 47.3214602 s
