// dafny-synthesis_task_id_279.dfy

method {:testEntry} NthDecagonalNumber(n: int) returns (decagonal: int)
  requires n >= 0
  ensures decagonal == 4 * n * n - 3 * n
{
  decagonal := (4 - n) * n - 3 * n;
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(0);
expect r0 == 4 * 0 * 0 - 3 * 0;
}

// REPEAT 1 - TIME: 2.3748835 s

method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(1);
expect r0 == 4 * 1 * 1 - 3 * 1;
}

// REPEAT 2 - TIME: 3.2466698 s

method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(2);
expect r0 == 4 * 2 * 2 - 3 * 2;
}

// REPEAT 3 - TIME: 4.0527317 s

method {:test} Test3() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(3);
expect r0 == 4 * 3 * 3 - 3 * 3;
}

// REPEAT 4 - TIME: 4.9407375 s

method {:test} Test4() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(4);
expect r0 == 4 * 4 * 4 - 3 * 4;
}

// REPEAT 5 - TIME: 5.8593873 s

method {:test} Test5() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(5);
expect r0 == 4 * 5 * 5 - 3 * 5;
}

// REPEAT 6 - TIME: 6.760359 s

method {:test} Test6() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(6);
expect r0 == 4 * 6 * 6 - 3 * 6;
}

// REPEAT 7 - TIME: 7.4982092 s

method {:test} Test7() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(7);
expect r0 == 4 * 7 * 7 - 3 * 7;
}

// REPEAT 8 - TIME: 8.2546985 s

method {:test} Test8() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(8);
expect r0 == 4 * 8 * 8 - 3 * 8;
}

// REPEAT 9 - TIME: 8.9749351 s

method {:test} Test9() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(9);
expect r0 == 4 * 9 * 9 - 3 * 9;
}

// REPEAT 10 - TIME: 9.727008 s
