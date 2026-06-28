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
var r0 := Min(-1, 0);
expect r0 <= -1 && r0 <= 0;
expect r0 == -1 || r0 == 0;
}
method {:test} Test3() {
var r0 := Max(0, 0);
}
method {:test} Test4() {
var r0 := Max(-1, 0);
}
method {:test} Test5() {
var r0, r1 := MaxSum(0, 0);
expect r0 == 0 + 0;
expect r1 == if 0 >= 0 then 0 else 0;
}
method {:test} Test6() {
var r0, r1 := MaxSum(-1, 0);
expect r0 == -1 + 0;
expect r1 == if -1 >= 0 then -1 else 0;
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
TestMaxSum(-1, 0);
}
method {:test} Test10() {
TestMaxSum(8854, 8855);
}

// REPEAT 1 - TIME: 18.7216572 s

method {:test} Test11() {
expect 1 <= 2474, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(2474);
expect 0 <= r0 < 2474;
}
method {:test} Test12() {
var r0 := Min(1, 1);
expect r0 <= 1 && r0 <= 1;
expect r0 == 1 || r0 == 1;
}
method {:test} Test13() {
var r0 := Min(1, 2);
expect r0 <= 1 && r0 <= 2;
expect r0 == 1 || r0 == 2;
}
method {:test} Test14() {
var r0 := Max(1, 1);
}
method {:test} Test15() {
var r0 := Max(1, 2);
}
method {:test} Test16() {
var r0, r1 := MaxSum(1, 1);
expect r0 == 1 + 1;
expect r1 == if 1 >= 1 then 1 else 1;
}
method {:test} Test17() {
var r0, r1 := MaxSum(1, 2);
expect r0 == 1 + 2;
expect r1 == if 1 >= 2 then 1 else 2;
}
method {:test} Test18() {
expect 39 <= 2 * 39, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(39, 39);
expect 39 == r0 + r1;
expect (39 == r0 || 39 == r1) && r0 <= 39 && r1 <= 39;
}
method {:test} Test19() {
TestMaxSum(8855, 8856);
}

// REPEAT 2 - TIME: 31.1823512 s

method {:test} Test21() {
expect 1 <= 2476, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(2476);
expect 0 <= r0 < 2476;
}
method {:test} Test22() {
var r0 := Min(3, 3);
expect r0 <= 3 && r0 <= 3;
expect r0 == 3 || r0 == 3;
}
method {:test} Test23() {
var r0 := Min(2, 3);
expect r0 <= 2 && r0 <= 3;
expect r0 == 2 || r0 == 3;
}
method {:test} Test24() {
var r0 := Max(3, 3);
}
method {:test} Test25() {
var r0 := Max(2, 3);
}
method {:test} Test26() {
var r0, r1 := MaxSum(3, 3);
expect r0 == 3 + 3;
expect r1 == if 3 >= 3 then 3 else 3;
}
method {:test} Test27() {
var r0, r1 := MaxSum(2, 3);
expect r0 == 2 + 3;
expect r1 == if 2 >= 3 then 2 else 3;
}
method {:test} Test28() {
expect 40 <= 2 * 40, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(40, 40);
expect 40 == r0 + r1;
expect (40 == r0 || 40 == r1) && r0 <= 40 && r1 <= 40;
}
method {:test} Test29() {
TestMaxSum(8856, 8857);
}

// REPEAT 3 - TIME: 46.567905 s

method {:test} Test31() {
expect 1 <= 2478, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(2478);
expect 0 <= r0 < 2478;
}
method {:test} Test32() {
var r0 := Min(4, 4);
expect r0 <= 4 && r0 <= 4;
expect r0 == 4 || r0 == 4;
}
method {:test} Test33() {
var r0 := Min(4, 5);
expect r0 <= 4 && r0 <= 5;
expect r0 == 4 || r0 == 5;
}
method {:test} Test34() {
var r0 := Max(4, 4);
}
method {:test} Test35() {
var r0 := Max(4, 5);
}
method {:test} Test36() {
var r0, r1 := MaxSum(4, 4);
expect r0 == 4 + 4;
expect r1 == if 4 >= 4 then 4 else 4;
}
method {:test} Test37() {
var r0, r1 := MaxSum(4, 5);
expect r0 == 4 + 5;
expect r1 == if 4 >= 5 then 4 else 5;
}
method {:test} Test38() {
expect 41 <= 2 * 41, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(41, 41);
expect 41 == r0 + r1;
expect (41 == r0 || 41 == r1) && r0 <= 41 && r1 <= 41;
}
method {:test} Test39() {
TestMaxSum(8857, 8858);
}

// REPEAT 4 - TIME: 62.8629034 s

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

// REPEAT 6 - TIME: 99.2989507 s

method {:test} Test61() {
expect 1 <= 2484, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(2484);
expect 0 <= r0 < 2484;
}
method {:test} Test62() {
var r0 := Min(9, 9);
expect r0 <= 9 && r0 <= 9;
expect r0 == 9 || r0 == 9;
}
method {:test} Test63() {
var r0 := Min(8, 9);
expect r0 <= 8 && r0 <= 9;
expect r0 == 8 || r0 == 9;
}
method {:test} Test64() {
var r0 := Max(9, 9);
}
method {:test} Test65() {
var r0 := Max(8, 9);
}
method {:test} Test66() {
var r0, r1 := MaxSum(9, 9);
expect r0 == 9 + 9;
expect r1 == if 9 >= 9 then 9 else 9;
}
method {:test} Test67() {
var r0, r1 := MaxSum(8, 9);
expect r0 == 8 + 9;
expect r1 == if 8 >= 9 then 8 else 9;
}
method {:test} Test68() {
expect 44 <= 2 * 44, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(44, 44);
expect 44 == r0 + r1;
expect (44 == r0 || 44 == r1) && r0 <= 44 && r1 <= 44;
}
method {:test} Test69() {
TestMaxSum(8860, 8861);
}

// REPEAT 7 - TIME: 121.0701737 s

method {:test} Test71() {
expect 1 <= 2486, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(2486);
expect 0 <= r0 < 2486;
}
method {:test} Test72() {
var r0 := Min(10, 10);
expect r0 <= 10 && r0 <= 10;
expect r0 == 10 || r0 == 10;
}
method {:test} Test73() {
var r0 := Min(10, 11);
expect r0 <= 10 && r0 <= 11;
expect r0 == 10 || r0 == 11;
}
method {:test} Test74() {
var r0 := Max(10, 10);
}
method {:test} Test75() {
var r0 := Max(10, 11);
}
method {:test} Test76() {
var r0, r1 := MaxSum(10, 10);
expect r0 == 10 + 10;
expect r1 == if 10 >= 10 then 10 else 10;
}
method {:test} Test77() {
var r0, r1 := MaxSum(10, 11);
expect r0 == 10 + 11;
expect r1 == if 10 >= 11 then 10 else 11;
}
method {:test} Test78() {
expect 45 <= 2 * 45, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(45, 45);
expect 45 == r0 + r1;
expect (45 == r0 || 45 == r1) && r0 <= 45 && r1 <= 45;
}
method {:test} Test79() {
TestMaxSum(8861, 8862);
}

// REPEAT 8 - TIME: 140.1090418 s

method {:test} Test81() {
expect 1 <= 2488, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(2488);
expect 0 <= r0 < 2488;
}
method {:test} Test82() {
var r0 := Min(12, 12);
expect r0 <= 12 && r0 <= 12;
expect r0 == 12 || r0 == 12;
}
method {:test} Test83() {
var r0 := Min(11, 12);
expect r0 <= 11 && r0 <= 12;
expect r0 == 11 || r0 == 12;
}
method {:test} Test84() {
var r0 := Max(12, 12);
}
method {:test} Test85() {
var r0 := Max(11, 12);
}
method {:test} Test86() {
var r0, r1 := MaxSum(12, 12);
expect r0 == 12 + 12;
expect r1 == if 12 >= 12 then 12 else 12;
}
method {:test} Test87() {
var r0, r1 := MaxSum(11, 12);
expect r0 == 11 + 12;
expect r1 == if 11 >= 12 then 11 else 12;
}
method {:test} Test88() {
expect 46 <= 2 * 46, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(46, 46);
expect 46 == r0 + r1;
expect (46 == r0 || 46 == r1) && r0 <= 46 && r1 <= 46;
}
method {:test} Test89() {
TestMaxSum(8862, 8863);
}

// REPEAT 9 - TIME: 160.1776651 s

method {:test} Test91() {
expect 1 <= 2490, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Index(2490);
expect 0 <= r0 < 2490;
}
method {:test} Test92() {
var r0 := Min(13, 13);
expect r0 <= 13 && r0 <= 13;
expect r0 == 13 || r0 == 13;
}
method {:test} Test93() {
var r0 := Min(13, 14);
expect r0 <= 13 && r0 <= 14;
expect r0 == 13 || r0 == 14;
}
method {:test} Test94() {
var r0 := Max(13, 13);
}
method {:test} Test95() {
var r0 := Max(13, 14);
}
method {:test} Test96() {
var r0, r1 := MaxSum(13, 13);
expect r0 == 13 + 13;
expect r1 == if 13 >= 13 then 13 else 13;
}
method {:test} Test97() {
var r0, r1 := MaxSum(13, 14);
expect r0 == 13 + 14;
expect r1 == if 13 >= 14 then 13 else 14;
}
method {:test} Test98() {
expect 47 <= 2 * 47, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := ReconstructFromMaxSum(47, 47);
expect 47 == r0 + r1;
expect (47 == r0 || 47 == r1) && r0 <= 47 && r1 <= 47;
}
method {:test} Test99() {
TestMaxSum(8863, 8864);
}

// REPEAT 10 - TIME: 183.4622747 s
