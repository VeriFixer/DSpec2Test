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

method {:test} Test8() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(5, 5, 4);
expect r0 <= 5 && r0 <= 5 && r0 <= 4;
}
method {:test} Test9() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(3, 5, 4);
expect r0 <= 3 && r0 <= 5 && r0 <= 4;
}
method {:test} Test10() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(3, 4, 4);
expect r0 <= 3 && r0 <= 4 && r0 <= 4;
}
method {:test} Test11() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(4, 4, 4);
expect r0 <= 4 && r0 <= 4 && r0 <= 4;
}

// REPEAT 3 - TIME: 8.2300977 s
