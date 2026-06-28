// cs245-verification_tmp_tmp0h_nxhqp_A8_Q2.dfy

method {:testEntry} A8Q1(x: int, y: int, z: int)
    returns (m: int)
  requires true
  ensures m <= x && m <= y && m <= z
{
  if z < y {
    if z != x {
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

method {:test} Test17() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(106, 106, 106);
expect r0 <= 106 && r0 <= 106 && r0 <= 106;
}

// REPEAT 7 - TIME: 15.8000791 s
