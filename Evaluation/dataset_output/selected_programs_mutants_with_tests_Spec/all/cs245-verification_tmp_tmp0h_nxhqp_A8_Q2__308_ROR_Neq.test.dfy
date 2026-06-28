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
var r0 := A8Q1(0, 0, 0);
expect r0 <= 0 && r0 <= 0 && r0 <= 0;
}

// REPEAT 1 - TIME: 2.8550715 s

method {:test} Test1() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(1, 1, 1);
expect r0 <= 1 && r0 <= 1 && r0 <= 1;
}

// REPEAT 2 - TIME: 3.8152168 s

method {:test} Test2() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(2, 2, 2);
expect r0 <= 2 && r0 <= 2 && r0 <= 2;
}

// REPEAT 3 - TIME: 4.7000913 s

method {:test} Test3() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(3, 3, 3);
expect r0 <= 3 && r0 <= 3 && r0 <= 3;
}

// REPEAT 4 - TIME: 5.5655429 s

method {:test} Test4() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(4, 4, 4);
expect r0 <= 4 && r0 <= 4 && r0 <= 4;
}

// REPEAT 5 - TIME: 6.3771759 s

method {:test} Test5() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(5, 5, 5);
expect r0 <= 5 && r0 <= 5 && r0 <= 5;
}

// REPEAT 6 - TIME: 7.2241354 s

method {:test} Test6() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(6, 6, 6);
expect r0 <= 6 && r0 <= 6 && r0 <= 6;
}

// REPEAT 7 - TIME: 8.1198106 s

method {:test} Test7() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(7, 7, 7);
expect r0 <= 7 && r0 <= 7 && r0 <= 7;
}

// REPEAT 8 - TIME: 9.0350565 s

method {:test} Test8() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(8, 8, 8);
expect r0 <= 8 && r0 <= 8 && r0 <= 8;
}

// REPEAT 9 - TIME: 9.8748503 s

method {:test} Test9() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(9, 9, 9);
expect r0 <= 9 && r0 <= 9 && r0 <= 9;
}

// REPEAT 10 - TIME: 10.6456712 s
