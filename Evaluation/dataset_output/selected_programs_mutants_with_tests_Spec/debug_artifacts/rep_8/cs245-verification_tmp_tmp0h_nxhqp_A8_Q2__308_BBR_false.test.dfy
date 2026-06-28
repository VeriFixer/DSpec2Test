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

method {:test} Test7() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(7, 7, 7);
expect r0 <= 7 && r0 <= 7 && r0 <= 7;
}

// REPEAT 8 - TIME: 9.0350565 s
