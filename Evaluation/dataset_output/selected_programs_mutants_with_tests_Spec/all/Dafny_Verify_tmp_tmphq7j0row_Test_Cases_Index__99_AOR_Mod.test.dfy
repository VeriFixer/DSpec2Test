// Dafny_Verify_tmp_tmphq7j0row_Test_Cases_Index.dfy

method {:testEntry} Index(n: int) returns (i: int)
  requires 1 <= n
  ensures 0 <= i < n
{
  i := n % 2;
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

// REPEAT 1 - TIME: 6.46346 s

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

method {:test} Test17() {
expect 1 <= 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(3);
expect 0 <= r0 < 3;
}
method {:test} Test18() {
var r0 := Min(3, 3);
expect r0 <= 3 && r0 <= 3;
expect r0 == 3 || r0 == 3;
}
method {:test} Test19() {
var r0 := Min(4, 3);
expect r0 <= 4 && r0 <= 3;
expect r0 == 4 || r0 == 3;
}
method {:test} Test20() {
var r0 := Max(27, 26);
}
method {:test} Test21() {
var r0, r1 := MaxSum(7720, 7721);
expect r0 == 7720 + 7721;
expect r1 == if 7720 >= 7721 then 7720 else 7721;
}
method {:test} Test22() {
expect 15442 <= 2 * 7721, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15442, 7721);
expect 15442 == r0 + r1;
expect (7721 == r0 || 7721 == r1) && r0 <= 7721 && r1 <= 7721;
}
method {:test} Test23() {
expect 15441 <= 2 * 7721, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15441, 7721);
expect 15441 == r0 + r1;
expect (7721 == r0 || 7721 == r1) && r0 <= 7721 && r1 <= 7721;
}
method {:test} Test24() {
TestMaxSum(27, 26);
}

// REPEAT 3 - TIME: 13.9234754 s

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

method {:test} Test33() {
expect 1 <= 5, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(5);
expect 0 <= r0 < 5;
}
method {:test} Test34() {
var r0 := Min(6, 6);
expect r0 <= 6 && r0 <= 6;
expect r0 == 6 || r0 == 6;
}
method {:test} Test35() {
var r0 := Min(7, 6);
expect r0 <= 7 && r0 <= 6;
expect r0 == 7 || r0 == 6;
}
method {:test} Test36() {
var r0 := Max(31, 30);
}
method {:test} Test37() {
var r0, r1 := MaxSum(7722, 7723);
expect r0 == 7722 + 7723;
expect r1 == if 7722 >= 7723 then 7722 else 7723;
}
method {:test} Test38() {
expect 15446 <= 2 * 7723, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15446, 7723);
expect 15446 == r0 + r1;
expect (7723 == r0 || 7723 == r1) && r0 <= 7723 && r1 <= 7723;
}
method {:test} Test39() {
expect 15445 <= 2 * 7723, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15445, 7723);
expect 15445 == r0 + r1;
expect (7723 == r0 || 7723 == r1) && r0 <= 7723 && r1 <= 7723;
}
method {:test} Test40() {
TestMaxSum(31, 30);
}

// REPEAT 5 - TIME: 20.7342375 s

method {:test} Test41() {
expect 1 <= 6, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(6);
expect 0 <= r0 < 6;
}
method {:test} Test42() {
var r0 := Min(8, 8);
expect r0 <= 8 && r0 <= 8;
expect r0 == 8 || r0 == 8;
}
method {:test} Test43() {
var r0 := Min(8, 7);
expect r0 <= 8 && r0 <= 7;
expect r0 == 8 || r0 == 7;
}
method {:test} Test44() {
var r0 := Max(32, 33);
}
method {:test} Test45() {
var r0, r1 := MaxSum(7723, 7724);
expect r0 == 7723 + 7724;
expect r1 == if 7723 >= 7724 then 7723 else 7724;
}
method {:test} Test46() {
expect 15448 <= 2 * 7724, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15448, 7724);
expect 15448 == r0 + r1;
expect (7724 == r0 || 7724 == r1) && r0 <= 7724 && r1 <= 7724;
}
method {:test} Test47() {
expect 15447 <= 2 * 7724, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15447, 7724);
expect 15447 == r0 + r1;
expect (7724 == r0 || 7724 == r1) && r0 <= 7724 && r1 <= 7724;
}
method {:test} Test48() {
TestMaxSum(33, 32);
}

// REPEAT 6 - TIME: 24.2166908 s

method {:test} Test49() {
expect 1 <= 7, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(7);
expect 0 <= r0 < 7;
}
method {:test} Test50() {
var r0 := Min(9, 9);
expect r0 <= 9 && r0 <= 9;
expect r0 == 9 || r0 == 9;
}
method {:test} Test51() {
var r0 := Min(10, 9);
expect r0 <= 10 && r0 <= 9;
expect r0 == 10 || r0 == 9;
}
method {:test} Test52() {
var r0 := Max(34, 35);
}
method {:test} Test53() {
var r0, r1 := MaxSum(7724, 7725);
expect r0 == 7724 + 7725;
expect r1 == if 7724 >= 7725 then 7724 else 7725;
}
method {:test} Test54() {
expect 15450 <= 2 * 7725, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15450, 7725);
expect 15450 == r0 + r1;
expect (7725 == r0 || 7725 == r1) && r0 <= 7725 && r1 <= 7725;
}
method {:test} Test55() {
expect 15449 <= 2 * 7725, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15449, 7725);
expect 15449 == r0 + r1;
expect (7725 == r0 || 7725 == r1) && r0 <= 7725 && r1 <= 7725;
}
method {:test} Test56() {
TestMaxSum(35, 34);
}

// REPEAT 7 - TIME: 27.2081652 s

method {:test} Test57() {
expect 1 <= 8, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(8);
expect 0 <= r0 < 8;
}
method {:test} Test58() {
var r0 := Min(11, 11);
expect r0 <= 11 && r0 <= 11;
expect r0 == 11 || r0 == 11;
}
method {:test} Test59() {
var r0 := Min(11, 10);
expect r0 <= 11 && r0 <= 10;
expect r0 == 11 || r0 == 10;
}
method {:test} Test60() {
var r0 := Max(36, 37);
}
method {:test} Test61() {
var r0, r1 := MaxSum(7725, 7726);
expect r0 == 7725 + 7726;
expect r1 == if 7725 >= 7726 then 7725 else 7726;
}
method {:test} Test62() {
expect 15452 <= 2 * 7726, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15452, 7726);
expect 15452 == r0 + r1;
expect (7726 == r0 || 7726 == r1) && r0 <= 7726 && r1 <= 7726;
}
method {:test} Test63() {
expect 15451 <= 2 * 7726, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15451, 7726);
expect 15451 == r0 + r1;
expect (7726 == r0 || 7726 == r1) && r0 <= 7726 && r1 <= 7726;
}
method {:test} Test64() {
TestMaxSum(37, 36);
}

// REPEAT 8 - TIME: 30.4295117 s

method {:test} Test65() {
expect 1 <= 9, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(9);
expect 0 <= r0 < 9;
}
method {:test} Test66() {
var r0 := Min(12, 12);
expect r0 <= 12 && r0 <= 12;
expect r0 == 12 || r0 == 12;
}
method {:test} Test67() {
var r0 := Min(13, 12);
expect r0 <= 13 && r0 <= 12;
expect r0 == 13 || r0 == 12;
}
method {:test} Test68() {
var r0 := Max(39, 38);
}
method {:test} Test69() {
var r0, r1 := MaxSum(7726, 7727);
expect r0 == 7726 + 7727;
expect r1 == if 7726 >= 7727 then 7726 else 7727;
}
method {:test} Test70() {
expect 15454 <= 2 * 7727, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15454, 7727);
expect 15454 == r0 + r1;
expect (7727 == r0 || 7727 == r1) && r0 <= 7727 && r1 <= 7727;
}
method {:test} Test71() {
expect 15453 <= 2 * 7727, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15453, 7727);
expect 15453 == r0 + r1;
expect (7727 == r0 || 7727 == r1) && r0 <= 7727 && r1 <= 7727;
}
method {:test} Test72() {
TestMaxSum(39, 38);
}

// REPEAT 9 - TIME: 33.4337825 s

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

// REPEAT 10 - TIME: 36.1168041 s
