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

method {:test} Test36() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(18, 18, 17);
expect r0 <= 18 && r0 <= 18 && r0 <= 17;
}
method {:test} Test37() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(18, 19, 18);
expect r0 <= 18 && r0 <= 19 && r0 <= 18;
}
method {:test} Test38() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(18, 19, 19);
expect r0 <= 18 && r0 <= 19 && r0 <= 19;
}
method {:test} Test39() {
expect true, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(18, 18, 18);
expect r0 <= 18 && r0 <= 18 && r0 <= 18;
}

// REPEAT 10 - TIME: 20.5779691 s
