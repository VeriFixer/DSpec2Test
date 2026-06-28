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
