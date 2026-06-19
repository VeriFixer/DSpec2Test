// cs245-verification_tmp_tmp0h_nxhqp_Assignments_simple.dfy

method {:testEntry} simple(y: int) returns (x: int)
  requires y == 6
  ensures x == 7
{
  assert y + 1 == 7;
  x := y - 1;
}


method {:test} Test0() {
expect 6 == 6, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := simple(6);
expect r0 == 7;
}

// REPEAT 1 - TIME: 4.1472169 s
