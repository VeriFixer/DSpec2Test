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

method {:test} Test87() {
expect 1 <= 102, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(102);
expect 0 <= r0 < 102;
}
method {:test} Test88() {
var r0 := Min(102, 102);
expect r0 <= 102 && r0 <= 102;
expect r0 == 102 || r0 == 102;
}
method {:test} Test89() {
var r0 := Min(102, 101);
expect r0 <= 102 && r0 <= 101;
expect r0 == 102 || r0 == 101;
}
method {:test} Test90() {
var r0 := Max(24, 25);
}
method {:test} Test91() {
var r0, r1 := MaxSum(7719, 7720);
expect r0 == 7719 + 7720;
expect r1 == if 7719 >= 7720 then 7719 else 7720;
}
method {:test} Test92() {
expect 15440 <= 2 * 7720, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15440, 7720);
expect 15440 == r0 + r1;
expect (7720 == r0 || 7720 == r1) && r0 <= 7720 && r1 <= 7720;
}
method {:test} Test93() {
expect 15439 <= 2 * 7720, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15439, 7720);
expect 15439 == r0 + r1;
expect (7720 == r0 || 7720 == r1) && r0 <= 7720 && r1 <= 7720;
}
method {:test} Test94() {
TestMaxSum(25, 24);
}

// REPEAT 2 - TIME: 51.7367497 s

method {:test} Test95() {
expect 1 <= 103, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(103);
expect 0 <= r0 < 103;
}
method {:test} Test96() {
var r0 := Min(103, 103);
expect r0 <= 103 && r0 <= 103;
expect r0 == 103 || r0 == 103;
}
method {:test} Test97() {
var r0 := Min(104, 103);
expect r0 <= 104 && r0 <= 103;
expect r0 == 104 || r0 == 103;
}
method {:test} Test98() {
var r0 := Max(27, 26);
}
method {:test} Test99() {
var r0, r1 := MaxSum(7720, 7721);
expect r0 == 7720 + 7721;
expect r1 == if 7720 >= 7721 then 7720 else 7721;
}
method {:test} Test100() {
expect 15442 <= 2 * 7721, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15442, 7721);
expect 15442 == r0 + r1;
expect (7721 == r0 || 7721 == r1) && r0 <= 7721 && r1 <= 7721;
}
method {:test} Test101() {
expect 15441 <= 2 * 7721, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15441, 7721);
expect 15441 == r0 + r1;
expect (7721 == r0 || 7721 == r1) && r0 <= 7721 && r1 <= 7721;
}
method {:test} Test102() {
TestMaxSum(27, 26);
}

// REPEAT 3 - TIME: 55.6898558 s

method {:test} Test103() {
expect 1 <= 104, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(104);
expect 0 <= r0 < 104;
}
method {:test} Test104() {
var r0 := Min(105, 105);
expect r0 <= 105 && r0 <= 105;
expect r0 == 105 || r0 == 105;
}
method {:test} Test105() {
var r0 := Min(105, 104);
expect r0 <= 105 && r0 <= 104;
expect r0 == 105 || r0 == 104;
}
method {:test} Test106() {
var r0 := Max(29, 28);
}
method {:test} Test107() {
var r0, r1 := MaxSum(7721, 7722);
expect r0 == 7721 + 7722;
expect r1 == if 7721 >= 7722 then 7721 else 7722;
}
method {:test} Test108() {
expect 15443 <= 2 * 7722, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15443, 7722);
expect 15443 == r0 + r1;
expect (7722 == r0 || 7722 == r1) && r0 <= 7722 && r1 <= 7722;
}
method {:test} Test110() {
TestMaxSum(29, 28);
}

// REPEAT 4 - TIME: 59.3622455 s

method {:test} Test111() {
expect 1 <= 105, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(105);
expect 0 <= r0 < 105;
}
method {:test} Test112() {
var r0 := Min(106, 106);
expect r0 <= 106 && r0 <= 106;
expect r0 == 106 || r0 == 106;
}
method {:test} Test113() {
var r0 := Min(107, 106);
expect r0 <= 107 && r0 <= 106;
expect r0 == 107 || r0 == 106;
}
method {:test} Test114() {
var r0 := Max(31, 30);
}
method {:test} Test115() {
var r0, r1 := MaxSum(7722, 7723);
expect r0 == 7722 + 7723;
expect r1 == if 7722 >= 7723 then 7722 else 7723;
}
method {:test} Test116() {
expect 15444 <= 2 * 7723, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15444, 7723);
expect 15444 == r0 + r1;
expect (7723 == r0 || 7723 == r1) && r0 <= 7723 && r1 <= 7723;
}
method {:test} Test117() {
expect 15445 <= 2 * 7723, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15445, 7723);
expect 15445 == r0 + r1;
expect (7723 == r0 || 7723 == r1) && r0 <= 7723 && r1 <= 7723;
}
method {:test} Test118() {
TestMaxSum(31, 30);
}

// REPEAT 5 - TIME: 63.5676637 s

method {:test} Test119() {
expect 1 <= 106, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(106);
expect 0 <= r0 < 106;
}
method {:test} Test120() {
var r0 := Min(108, 108);
expect r0 <= 108 && r0 <= 108;
expect r0 == 108 || r0 == 108;
}
method {:test} Test121() {
var r0 := Min(108, 107);
expect r0 <= 108 && r0 <= 107;
expect r0 == 108 || r0 == 107;
}
method {:test} Test122() {
var r0 := Max(33, 32);
}
method {:test} Test123() {
var r0, r1 := MaxSum(7723, 7724);
expect r0 == 7723 + 7724;
expect r1 == if 7723 >= 7724 then 7723 else 7724;
}
method {:test} Test124() {
expect 15448 <= 2 * 7724, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15448, 7724);
expect 15448 == r0 + r1;
expect (7724 == r0 || 7724 == r1) && r0 <= 7724 && r1 <= 7724;
}
method {:test} Test125() {
expect 15447 <= 2 * 7724, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15447, 7724);
expect 15447 == r0 + r1;
expect (7724 == r0 || 7724 == r1) && r0 <= 7724 && r1 <= 7724;
}
method {:test} Test126() {
TestMaxSum(33, 32);
}

// REPEAT 6 - TIME: 66.8015675 s

method {:test} Test127() {
expect 1 <= 107, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(107);
expect 0 <= r0 < 107;
}
method {:test} Test128() {
var r0 := Min(109, 109);
expect r0 <= 109 && r0 <= 109;
expect r0 == 109 || r0 == 109;
}
method {:test} Test129() {
var r0 := Min(110, 109);
expect r0 <= 110 && r0 <= 109;
expect r0 == 110 || r0 == 109;
}
method {:test} Test130() {
var r0 := Max(35, 34);
}
method {:test} Test131() {
var r0, r1 := MaxSum(7724, 7725);
expect r0 == 7724 + 7725;
expect r1 == if 7724 >= 7725 then 7724 else 7725;
}
method {:test} Test132() {
expect 15449 <= 2 * 7725, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15449, 7725);
expect 15449 == r0 + r1;
expect (7725 == r0 || 7725 == r1) && r0 <= 7725 && r1 <= 7725;
}
method {:test} Test134() {
TestMaxSum(35, 34);
}

// REPEAT 7 - TIME: 70.2523176 s

method {:test} Test135() {
expect 1 <= 108, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(108);
expect 0 <= r0 < 108;
}
method {:test} Test136() {
var r0 := Min(111, 111);
expect r0 <= 111 && r0 <= 111;
expect r0 == 111 || r0 == 111;
}
method {:test} Test137() {
var r0 := Min(111, 110);
expect r0 <= 111 && r0 <= 110;
expect r0 == 111 || r0 == 110;
}
method {:test} Test138() {
var r0 := Max(37, 36);
}
method {:test} Test139() {
var r0, r1 := MaxSum(7725, 7726);
expect r0 == 7725 + 7726;
expect r1 == if 7725 >= 7726 then 7725 else 7726;
}
method {:test} Test140() {
expect 15450 <= 2 * 7726, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15450, 7726);
expect 15450 == r0 + r1;
expect (7726 == r0 || 7726 == r1) && r0 <= 7726 && r1 <= 7726;
}
method {:test} Test141() {
expect 15451 <= 2 * 7726, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15451, 7726);
expect 15451 == r0 + r1;
expect (7726 == r0 || 7726 == r1) && r0 <= 7726 && r1 <= 7726;
}
method {:test} Test142() {
TestMaxSum(37, 36);
}

// REPEAT 8 - TIME: 74.2072878 s

method {:test} Test143() {
expect 1 <= 109, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(109);
expect 0 <= r0 < 109;
}
method {:test} Test144() {
var r0 := Min(112, 112);
expect r0 <= 112 && r0 <= 112;
expect r0 == 112 || r0 == 112;
}
method {:test} Test145() {
var r0 := Min(113, 112);
expect r0 <= 113 && r0 <= 112;
expect r0 == 113 || r0 == 112;
}
method {:test} Test146() {
var r0 := Max(39, 38);
}
method {:test} Test147() {
var r0, r1 := MaxSum(7726, 7727);
expect r0 == 7726 + 7727;
expect r1 == if 7726 >= 7727 then 7726 else 7727;
}
method {:test} Test148() {
expect 15452 <= 2 * 7727, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15452, 7727);
expect 15452 == r0 + r1;
expect (7727 == r0 || 7727 == r1) && r0 <= 7727 && r1 <= 7727;
}
method {:test} Test149() {
expect 15453 <= 2 * 7727, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15453, 7727);
expect 15453 == r0 + r1;
expect (7727 == r0 || 7727 == r1) && r0 <= 7727 && r1 <= 7727;
}
method {:test} Test150() {
TestMaxSum(38, 39);
}

// REPEAT 9 - TIME: 77.5257203 s

method {:test} Test151() {
expect 1 <= 110, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(110);
expect 0 <= r0 < 110;
}
method {:test} Test152() {
var r0 := Min(114, 114);
expect r0 <= 114 && r0 <= 114;
expect r0 == 114 || r0 == 114;
}
method {:test} Test153() {
var r0 := Min(114, 113);
expect r0 <= 114 && r0 <= 113;
expect r0 == 114 || r0 == 113;
}
method {:test} Test154() {
var r0 := Max(41, 40);
}
method {:test} Test155() {
var r0, r1 := MaxSum(7727, 7728);
expect r0 == 7727 + 7728;
expect r1 == if 7727 >= 7728 then 7727 else 7728;
}
method {:test} Test156() {
expect 15456 <= 2 * 7728, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15456, 7728);
expect 15456 == r0 + r1;
expect (7728 == r0 || 7728 == r1) && r0 <= 7728 && r1 <= 7728;
}
method {:test} Test157() {
expect 15455 <= 2 * 7728, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(15455, 7728);
expect 15455 == r0 + r1;
expect (7728 == r0 || 7728 == r1) && r0 <= 7728 && r1 <= 7728;
}
method {:test} Test158() {
TestMaxSum(40, 41);
}

// REPEAT 10 - TIME: 81.1243302 s
