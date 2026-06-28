// Dafny_Verify_tmp_tmphq7j0row_Fine_Tune_Examples_error_data_completion_11.dfy

method {:testEntry} main(x: int) returns (j: int, i: int)
  requires x > 0
  ensures j == 2 * x
{
  i := 0;
  j := 0;
  while true
    invariant 0 <= i <= x
    invariant j == 2 * i
  {
    j := j + 2;
    i := i + 1;
  }
}


method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(1);
expect r0 == 2 * 1;
}

// REPEAT 1 - TIME: 3.1663253 s

method {:test} Test1() {
expect 40 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(40);
expect r0 == 2 * 40;
}

// REPEAT 2 - TIME: 4.1342728 s

method {:test} Test2() {
expect 41 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(41);
expect r0 == 2 * 41;
}

// REPEAT 3 - TIME: 5.1420074 s

method {:test} Test3() {
expect 42 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(42);
expect r0 == 2 * 42;
}

// REPEAT 4 - TIME: 6.1672305 s

method {:test} Test4() {
expect 43 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(43);
expect r0 == 2 * 43;
}

// REPEAT 5 - TIME: 7.0962547 s

method {:test} Test5() {
expect 44 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(44);
expect r0 == 2 * 44;
}

// REPEAT 6 - TIME: 7.8986022 s

method {:test} Test6() {
expect 45 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(45);
expect r0 == 2 * 45;
}

// REPEAT 7 - TIME: 8.6934015 s

method {:test} Test7() {
expect 46 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(46);
expect r0 == 2 * 46;
}

// REPEAT 8 - TIME: 9.3469342 s

method {:test} Test8() {
expect 47 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(47);
expect r0 == 2 * 47;
}

// REPEAT 9 - TIME: 10.093289 s

method {:test} Test9() {
expect 48 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(48);
expect r0 == 2 * 48;
}

// REPEAT 10 - TIME: 10.8576923 s
