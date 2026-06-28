// Dafny_Verify_tmp_tmphq7j0row_dataset_C_convert_examples_11.dfy

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

// REPEAT 1 - TIME: 2.9977153 s

method {:test} Test1() {
expect 40 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(40);
expect r0 == 2 * 40;
}

// REPEAT 2 - TIME: 3.9657068 s

method {:test} Test2() {
expect 41 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(41);
expect r0 == 2 * 41;
}

// REPEAT 3 - TIME: 4.8534027 s

method {:test} Test3() {
expect 42 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(42);
expect r0 == 2 * 42;
}

// REPEAT 4 - TIME: 5.7361705 s

method {:test} Test4() {
expect 43 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(43);
expect r0 == 2 * 43;
}

// REPEAT 5 - TIME: 6.6508434 s

method {:test} Test5() {
expect 44 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(44);
expect r0 == 2 * 44;
}

// REPEAT 6 - TIME: 7.4885187 s

method {:test} Test6() {
expect 45 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(45);
expect r0 == 2 * 45;
}

// REPEAT 7 - TIME: 8.1151811 s

method {:test} Test7() {
expect 46 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(46);
expect r0 == 2 * 46;
}

// REPEAT 8 - TIME: 8.8321015 s

method {:test} Test8() {
expect 47 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(47);
expect r0 == 2 * 47;
}

// REPEAT 9 - TIME: 9.4349205 s

method {:test} Test9() {
expect 48 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(48);
expect r0 == 2 * 48;
}

// REPEAT 10 - TIME: 9.9850048 s
