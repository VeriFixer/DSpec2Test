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
