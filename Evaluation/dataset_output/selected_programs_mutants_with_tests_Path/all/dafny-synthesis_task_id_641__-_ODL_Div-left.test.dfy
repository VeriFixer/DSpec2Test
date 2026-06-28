// dafny-synthesis_task_id_641.dfy

method {:testEntry} NthNonagonalNumber(n: int) returns (number: int)
  requires n >= 0
  ensures number == n * (7 * n - 5) / 2
{
  number := 2;
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(0);
expect r0 == 0 * (7 * 0 - 5) / 2;
}

// REPEAT 1 - TIME: 3.3185992 s

method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(1);
expect r0 == 1 * (7 * 1 - 5) / 2;
}

// REPEAT 2 - TIME: 4.4513923 s

method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(2);
expect r0 == 2 * (7 * 2 - 5) / 2;
}

// REPEAT 3 - TIME: 5.6217431 s

method {:test} Test3() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(3);
expect r0 == 3 * (7 * 3 - 5) / 2;
}

// REPEAT 4 - TIME: 6.8657592 s

method {:test} Test4() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(4);
expect r0 == 4 * (7 * 4 - 5) / 2;
}

// REPEAT 5 - TIME: 8.011171 s

method {:test} Test5() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(5);
expect r0 == 5 * (7 * 5 - 5) / 2;
}

// REPEAT 6 - TIME: 8.9681042 s

method {:test} Test6() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(6);
expect r0 == 6 * (7 * 6 - 5) / 2;
}

// REPEAT 7 - TIME: 9.8113397 s

method {:test} Test7() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(7);
expect r0 == 7 * (7 * 7 - 5) / 2;
}

// REPEAT 8 - TIME: 10.6845211 s

method {:test} Test8() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(8);
expect r0 == 8 * (7 * 8 - 5) / 2;
}

// REPEAT 9 - TIME: 11.5949805 s

method {:test} Test9() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(9);
expect r0 == 9 * (7 * 9 - 5) / 2;
}

// REPEAT 10 - TIME: 12.5944184 s
