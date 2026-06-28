// cs245-verification_tmp_tmp0h_nxhqp_A8_Q2.dfy

method {:testEntry} A8Q1(x: int, y: int, z: int)
    returns (m: int)
  requires true
  ensures m <= x && m <= y && m <= z
{
  if false {
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
var r0 := A8Q1(0, 0, 0);
expect r0 <= 0 && r0 <= 0 && r0 <= 0;
}
method {:test} Test1() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(-100, 0, 0);
expect r0 <= -100 && r0 <= 0 && r0 <= 0;
}
method {:test} Test2() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(100, 0, 0);
expect r0 <= 100 && r0 <= 0 && r0 <= 0;
}
method {:test} Test3() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(0, -100, 0);
expect r0 <= 0 && r0 <= -100 && r0 <= 0;
}
method {:test} Test4() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(0, 100, 0);
expect r0 <= 0 && r0 <= 100 && r0 <= 0;
}
method {:test} Test5() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(0, 0, -100);
expect r0 <= 0 && r0 <= 0 && r0 <= -100;
}
method {:test} Test6() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(0, 0, 100);
expect r0 <= 0 && r0 <= 0 && r0 <= 100;
}
method {:test} Test9() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(100, 100, 100);
expect r0 <= 100 && r0 <= 100 && r0 <= 100;
}

// REPEAT 1 - TIME: 10.2233576 s

method {:test} Test12() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(101, 101, 101);
expect r0 <= 101 && r0 <= 101 && r0 <= 101;
}

// REPEAT 2 - TIME: 11.1758854 s

method {:test} Test13() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(102, 102, 102);
expect r0 <= 102 && r0 <= 102 && r0 <= 102;
}

// REPEAT 3 - TIME: 12.2067053 s

method {:test} Test14() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(103, 103, 103);
expect r0 <= 103 && r0 <= 103 && r0 <= 103;
}

// REPEAT 4 - TIME: 13.0747558 s

method {:test} Test15() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(104, 104, 104);
expect r0 <= 104 && r0 <= 104 && r0 <= 104;
}

// REPEAT 5 - TIME: 14.0892641 s

method {:test} Test16() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(105, 105, 105);
expect r0 <= 105 && r0 <= 105 && r0 <= 105;
}

// REPEAT 6 - TIME: 14.9407274 s

method {:test} Test17() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(106, 106, 106);
expect r0 <= 106 && r0 <= 106 && r0 <= 106;
}

// REPEAT 7 - TIME: 15.8000791 s

method {:test} Test18() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(107, 107, 107);
expect r0 <= 107 && r0 <= 107 && r0 <= 107;
}

// REPEAT 8 - TIME: 16.6109698 s

method {:test} Test19() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(108, 108, 108);
expect r0 <= 108 && r0 <= 108 && r0 <= 108;
}

// REPEAT 9 - TIME: 17.3471242 s

method {:test} Test20() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(109, 109, 109);
expect r0 <= 109 && r0 <= 109 && r0 <= 109;
}

// REPEAT 10 - TIME: 18.1278974 s
