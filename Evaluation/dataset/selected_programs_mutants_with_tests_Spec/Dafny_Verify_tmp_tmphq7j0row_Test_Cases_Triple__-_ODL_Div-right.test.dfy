// Dafny_Verify_tmp_tmphq7j0row_Test_Cases_Triple.dfy

method {:testEntry} TripleConditions(x: int) returns (r: int)
  requires x % 2 == 0
  ensures r == 3 * x
{
  var y := x;
  r := 6 * y;
  assert r == 3 * x;
}

method {:test} Test0() {
expect 2472 % 2 == 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TripleConditions(2472);
expect r0 == 3 * 2472;
}
