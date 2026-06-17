// Dafny_Verify_tmp_tmphq7j0row_Fine_Tune_Examples_50_examples_41.dfy

method {:testEntry} main(n: int, k: int)
    returns (i: int, j: int)
  requires n >= 0
  requires k == 1 || k >= 0
  ensures k + i + j >= 2 * n
{
  i := 0;
  j := 0;
  while false
    invariant 0 <= i <= n
    invariant j == i * (i + 1) / 2
  {
    i := i + 1;
    j := j + i;
  }
}

method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 == 1 || 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(0, 1);
expect 1 + r0 + r1 >= 2 * 0;
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 == 1 || 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(100, 1);
expect 1 + r0 + r1 >= 2 * 100;
}
method {:test} Test4() {
expect 1236 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 == 1 || 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(1236, 1);
expect 1 + r0 + r1 >= 2 * 1236;
}
method {:test} Test5() {
expect 38 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 == 1 || 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(38, 1);
expect 1 + r0 + r1 >= 2 * 38;
}
method {:test} Test11() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2 == 1 || 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(0, 2);
expect 2 + r0 + r1 >= 2 * 0;
}
method {:test} Test13() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2 == 1 || 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(100, 2);
expect 2 + r0 + r1 >= 2 * 100;
}
method {:test} Test14() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 == 1 || 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(0, 0);
expect 0 + r0 + r1 >= 2 * 0;
}
method {:test} Test15() {
expect 38 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 100 == 1 || 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(38, 100);
expect 100 + r0 + r1 >= 2 * 38;
}
method {:test} Test17() {
expect 7719 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2 == 1 || 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7719, 2);
expect 2 + r0 + r1 >= 2 * 7719;
}
method {:test} Test18() {
expect 38 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2 == 1 || 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(38, 2);
expect 2 + r0 + r1 >= 2 * 38;
}

// REPEAT 1 - TIME: 12.8015043 s
