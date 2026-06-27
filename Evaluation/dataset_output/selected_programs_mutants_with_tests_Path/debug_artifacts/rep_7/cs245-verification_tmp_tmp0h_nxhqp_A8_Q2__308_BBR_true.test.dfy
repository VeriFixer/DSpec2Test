// cs245-verification_tmp_tmp0h_nxhqp_A8_Q2.dfy

method {:testEntry} A8Q1(x: int, y: int, z: int)
    returns (m: int)
  requires true
  ensures m <= x && m <= y && m <= z
{
  if true {
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

// REPEAT 7 - TIME: 14.2249948 s
