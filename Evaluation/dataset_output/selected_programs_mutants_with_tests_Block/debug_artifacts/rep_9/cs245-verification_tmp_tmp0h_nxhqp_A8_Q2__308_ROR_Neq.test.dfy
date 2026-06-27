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

method {:test} Test24() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(15, 16, 16);
expect r0 <= 15 && r0 <= 16 && r0 <= 16;
}
method {:test} Test25() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(15, 17, 16);
expect r0 <= 15 && r0 <= 17 && r0 <= 16;
}
method {:test} Test26() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(17, 17, 16);
expect r0 <= 17 && r0 <= 17 && r0 <= 16;
}

// REPEAT 9 - TIME: 14.3403084 s
