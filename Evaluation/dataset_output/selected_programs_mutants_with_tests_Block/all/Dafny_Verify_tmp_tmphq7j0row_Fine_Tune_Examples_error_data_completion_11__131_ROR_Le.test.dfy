// Dafny_Verify_tmp_tmphq7j0row_Fine_Tune_Examples_error_data_completion_11.dfy

method {:testEntry} main(x: int) returns (j: int, i: int)
  requires x > 0
  ensures j == 2 * x
{
  i := 0;
  j := 0;
  while i <= x
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

// REPEAT 1 - TIME: 1.9280615 s

method {:test} Test1() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(2);
expect r0 == 2 * 2;
}

// REPEAT 2 - TIME: 2.5913371 s

method {:test} Test2() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(3);
expect r0 == 2 * 3;
}

// REPEAT 3 - TIME: 3.17426 s

method {:test} Test3() {
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(4);
expect r0 == 2 * 4;
}

// REPEAT 4 - TIME: 3.8701845 s

method {:test} Test4() {
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(5);
expect r0 == 2 * 5;
}

// REPEAT 5 - TIME: 4.6124086 s

method {:test} Test5() {
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(6);
expect r0 == 2 * 6;
}

// REPEAT 6 - TIME: 5.2671264 s

method {:test} Test6() {
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7);
expect r0 == 2 * 7;
}

// REPEAT 7 - TIME: 5.9125651 s

method {:test} Test7() {
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(8);
expect r0 == 2 * 8;
}

// REPEAT 8 - TIME: 6.4031317 s

method {:test} Test8() {
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(9);
expect r0 == 2 * 9;
}

// REPEAT 9 - TIME: 7.0017187 s

method {:test} Test9() {
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(10);
expect r0 == 2 * 10;
}

// REPEAT 10 - TIME: 7.4858706 s
