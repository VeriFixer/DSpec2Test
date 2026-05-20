// Dafny_Verify_tmp_tmphq7j0row_Test_Cases_Triple.dfy

method {:testEntry} TripleConditions(x: int) returns (r: int)
  requires x % 2 == 0
  ensures r == 3 * x
{
  var y := x * 2;
  r := 6 * y;
  assert r == 3 * x;
}

method {:test} Test0() {
expect 3592 % 2 == 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TripleConditions(3592);
expect r0 == 3 * 3592;
}
method {:test} Test1() {
expect 3594 % 2 == 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TripleConditions(3594);
expect r0 == 3 * 3594;
}
method {:test} Test2() {
expect 3596 % 2 == 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TripleConditions(3596);
expect r0 == 3 * 3596;
}
method {:test} Test3() {
expect 3598 % 2 == 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TripleConditions(3598);
expect r0 == 3 * 3598;
}
method {:test} Test4() {
expect 3600 % 2 == 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TripleConditions(3600);
expect r0 == 3 * 3600;
}
