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
var r0 := A8Q1(7, 8, 8);
expect r0 <= 7 && r0 <= 8 && r0 <= 8;
}
method {:test} Test13() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(8, 9, 8);
expect r0 <= 8 && r0 <= 9 && r0 <= 8;
}
method {:test} Test14() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(9, 9, 8);
expect r0 <= 9 && r0 <= 9 && r0 <= 8;
}

// REPEAT 5 - TIME: 8.9628961 s
