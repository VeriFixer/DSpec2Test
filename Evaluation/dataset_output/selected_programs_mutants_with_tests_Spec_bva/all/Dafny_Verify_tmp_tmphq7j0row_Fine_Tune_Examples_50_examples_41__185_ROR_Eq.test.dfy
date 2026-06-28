// Dafny_Verify_tmp_tmphq7j0row_Fine_Tune_Examples_50_examples_41.dfy

method {:testEntry} main(n: int, k: int)
    returns (i: int, j: int)
  requires n >= 0
  requires k == 1 || k >= 0
  ensures k + i + j >= 2 * n
{
  i := 0;
  j := 0;
  while i == n
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

// REPEAT 1 - TIME: 17.3538979 s

method {:test} Test24() {
expect 7720 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 101 == 1 || 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7720, 101);
expect 101 + r0 + r1 >= 2 * 7720;
}

// REPEAT 2 - TIME: 18.7286877 s

method {:test} Test25() {
expect 7721 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 102 == 1 || 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7721, 102);
expect 102 + r0 + r1 >= 2 * 7721;
}

// REPEAT 3 - TIME: 19.8971846 s

method {:test} Test26() {
expect 7722 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 103 == 1 || 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7722, 103);
expect 103 + r0 + r1 >= 2 * 7722;
}

// REPEAT 4 - TIME: 21.0534146 s

method {:test} Test27() {
expect 7723 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 104 == 1 || 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7723, 104);
expect 104 + r0 + r1 >= 2 * 7723;
}

// REPEAT 5 - TIME: 22.339418 s

method {:test} Test28() {
expect 7724 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 105 == 1 || 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7724, 105);
expect 105 + r0 + r1 >= 2 * 7724;
}

// REPEAT 6 - TIME: 23.6851642 s

method {:test} Test29() {
expect 7725 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 106 == 1 || 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7725, 106);
expect 106 + r0 + r1 >= 2 * 7725;
}

// REPEAT 7 - TIME: 24.92701 s

method {:test} Test30() {
expect 7726 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 107 == 1 || 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7726, 107);
expect 107 + r0 + r1 >= 2 * 7726;
}

// REPEAT 8 - TIME: 26.1692556 s

method {:test} Test31() {
expect 7727 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 108 == 1 || 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7727, 108);
expect 108 + r0 + r1 >= 2 * 7727;
}

// REPEAT 9 - TIME: 27.2764813 s

method {:test} Test32() {
expect 7728 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 109 == 1 || 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7728, 109);
expect 109 + r0 + r1 >= 2 * 7728;
}

// REPEAT 10 - TIME: 28.2729085 s
