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
