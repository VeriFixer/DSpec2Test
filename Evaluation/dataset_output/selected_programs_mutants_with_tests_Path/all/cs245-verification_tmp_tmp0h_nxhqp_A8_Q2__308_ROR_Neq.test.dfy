// cs245-verification_tmp_tmp0h_nxhqp_A8_Q2.dfy

method {:testEntry} A8Q1(x: int, y: int, z: int)
    returns (m: int)
  requires true
  ensures m <= x && m <= y && m <= z
{
  if z != y {
    if z < x {
      m := z;
    } else {
      m := x;
    }
  } else {
    m := y;
    if x < y {
      m := x;
    }
  }
}


method {:test} Test0() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(1, 1, 0);
expect r0 <= 1 && r0 <= 1 && r0 <= 0;
}
method {:test} Test1() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(0, 1, 0);
expect r0 <= 0 && r0 <= 1 && r0 <= 0;
}
method {:test} Test2() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(-1, 0, 0);
expect r0 <= -1 && r0 <= 0 && r0 <= 0;
}
method {:test} Test3() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(0, 0, 0);
expect r0 <= 0 && r0 <= 0 && r0 <= 0;
}

// REPEAT 1 - TIME: 3.7366563 s

method {:test} Test4() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(2, 2, 1);
expect r0 <= 2 && r0 <= 2 && r0 <= 1;
}
method {:test} Test5() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(2, 3, 2);
expect r0 <= 2 && r0 <= 3 && r0 <= 2;
}
method {:test} Test6() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(2, 3, 3);
expect r0 <= 2 && r0 <= 3 && r0 <= 3;
}
method {:test} Test7() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(2, 2, 2);
expect r0 <= 2 && r0 <= 2 && r0 <= 2;
}

// REPEAT 2 - TIME: 6.0510897 s

method {:test} Test8() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(5, 5, 4);
expect r0 <= 5 && r0 <= 5 && r0 <= 4;
}
method {:test} Test9() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(3, 5, 4);
expect r0 <= 3 && r0 <= 5 && r0 <= 4;
}
method {:test} Test10() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(3, 4, 4);
expect r0 <= 3 && r0 <= 4 && r0 <= 4;
}
method {:test} Test11() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(4, 4, 4);
expect r0 <= 4 && r0 <= 4 && r0 <= 4;
}

// REPEAT 3 - TIME: 8.2300977 s

method {:test} Test12() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(6, 6, 5);
expect r0 <= 6 && r0 <= 6 && r0 <= 5;
}
method {:test} Test13() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(6, 7, 6);
expect r0 <= 6 && r0 <= 7 && r0 <= 6;
}
method {:test} Test14() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(6, 7, 7);
expect r0 <= 6 && r0 <= 7 && r0 <= 7;
}
method {:test} Test15() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(6, 6, 6);
expect r0 <= 6 && r0 <= 6 && r0 <= 6;
}

// REPEAT 4 - TIME: 10.0180732 s

method {:test} Test16() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(9, 9, 8);
expect r0 <= 9 && r0 <= 9 && r0 <= 8;
}
method {:test} Test17() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(7, 9, 8);
expect r0 <= 7 && r0 <= 9 && r0 <= 8;
}
method {:test} Test18() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(7, 8, 8);
expect r0 <= 7 && r0 <= 8 && r0 <= 8;
}
method {:test} Test19() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(8, 8, 8);
expect r0 <= 8 && r0 <= 8 && r0 <= 8;
}

// REPEAT 5 - TIME: 11.7751139 s

method {:test} Test20() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(10, 10, 9);
expect r0 <= 10 && r0 <= 10 && r0 <= 9;
}
method {:test} Test21() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(10, 11, 10);
expect r0 <= 10 && r0 <= 11 && r0 <= 10;
}
method {:test} Test22() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(10, 11, 11);
expect r0 <= 10 && r0 <= 11 && r0 <= 11;
}
method {:test} Test23() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(10, 10, 10);
expect r0 <= 10 && r0 <= 10 && r0 <= 10;
}

// REPEAT 6 - TIME: 13.4555664 s

method {:test} Test24() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(13, 13, 12);
expect r0 <= 13 && r0 <= 13 && r0 <= 12;
}
method {:test} Test25() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(11, 13, 12);
expect r0 <= 11 && r0 <= 13 && r0 <= 12;
}
method {:test} Test26() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(11, 12, 12);
expect r0 <= 11 && r0 <= 12 && r0 <= 12;
}
method {:test} Test27() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(12, 12, 12);
expect r0 <= 12 && r0 <= 12 && r0 <= 12;
}

// REPEAT 7 - TIME: 15.1331465 s

method {:test} Test28() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(14, 14, 13);
expect r0 <= 14 && r0 <= 14 && r0 <= 13;
}
method {:test} Test29() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(14, 15, 14);
expect r0 <= 14 && r0 <= 15 && r0 <= 14;
}
method {:test} Test30() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(14, 15, 15);
expect r0 <= 14 && r0 <= 15 && r0 <= 15;
}
method {:test} Test31() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(14, 14, 14);
expect r0 <= 14 && r0 <= 14 && r0 <= 14;
}

// REPEAT 8 - TIME: 16.8773473 s

method {:test} Test32() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(17, 17, 16);
expect r0 <= 17 && r0 <= 17 && r0 <= 16;
}
method {:test} Test33() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(15, 17, 16);
expect r0 <= 15 && r0 <= 17 && r0 <= 16;
}
method {:test} Test34() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(15, 16, 16);
expect r0 <= 15 && r0 <= 16 && r0 <= 16;
}
method {:test} Test35() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(16, 16, 16);
expect r0 <= 16 && r0 <= 16 && r0 <= 16;
}

// REPEAT 9 - TIME: 18.7675091 s

method {:test} Test36() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(18, 18, 17);
expect r0 <= 18 && r0 <= 18 && r0 <= 17;
}
method {:test} Test37() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(18, 19, 18);
expect r0 <= 18 && r0 <= 19 && r0 <= 18;
}
method {:test} Test38() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(18, 19, 19);
expect r0 <= 18 && r0 <= 19 && r0 <= 19;
}
method {:test} Test39() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(18, 18, 18);
expect r0 <= 18 && r0 <= 18 && r0 <= 18;
}

// REPEAT 10 - TIME: 20.5779691 s
