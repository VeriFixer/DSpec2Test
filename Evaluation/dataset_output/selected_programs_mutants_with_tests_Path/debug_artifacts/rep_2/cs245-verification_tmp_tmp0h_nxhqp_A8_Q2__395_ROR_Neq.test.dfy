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

method {:test} Test4() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(2, 2, 1);
expect r0 <= 2 && r0 <= 2 && r0 <= 1;
}
method {:test} Test5() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(2, 3, 2);
expect r0 <= 2 && r0 <= 3 && r0 <= 2;
}
method {:test} Test6() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(2, 3, 3);
expect r0 <= 2 && r0 <= 3 && r0 <= 3;
}
method {:test} Test7() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(2, 2, 2);
expect r0 <= 2 && r0 <= 2 && r0 <= 2;
}

// REPEAT 2 - TIME: 6.0510897 s
