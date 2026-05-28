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
expect 2472 % 2 == 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TripleConditions(2472);
expect r0 == 3 * 2472;
}
method {:test} Test1() {
expect -100 % 2 == 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TripleConditions(-100);
expect r0 == 3 * -100;
}
method {:test} Test2() {
expect 100 % 2 == 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TripleConditions(100);
expect r0 == 3 * 100;
}
method {:test} Test3() {
expect 15438 % 2 == 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TripleConditions(15438);
expect r0 == 3 * 15438;
}
method {:test} Test6() {
expect 15440 % 2 == 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TripleConditions(15440);
expect r0 == 3 * 15440;
}
method {:test} Test7() {
expect 15442 % 2 == 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TripleConditions(15442);
expect r0 == 3 * 15442;
}
method {:test} Test8() {
expect 15444 % 2 == 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TripleConditions(15444);
expect r0 == 3 * 15444;
}
method {:test} Test9() {
expect 15446 % 2 == 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TripleConditions(15446);
expect r0 == 3 * 15446;
}
method {:test} Test10() {
expect 15448 % 2 == 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TripleConditions(15448);
expect r0 == 3 * 15448;
}
method {:test} Test11() {
expect 15450 % 2 == 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TripleConditions(15450);
expect r0 == 3 * 15450;
}
