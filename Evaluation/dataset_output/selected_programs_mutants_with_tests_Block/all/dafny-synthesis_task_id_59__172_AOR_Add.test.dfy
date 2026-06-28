// dafny-synthesis_task_id_59.dfy

method {:testEntry} NthOctagonalNumber(n: int) returns (octagonalNumber: int)
  requires n >= 0
  ensures octagonalNumber == n * (3 * n - 2)
{
  octagonalNumber := n + (3 * n - 2);
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(0);
expect r0 == 0 * (3 * 0 - 2);
}

// REPEAT 1 - TIME: 2.3658305 s

method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(1);
expect r0 == 1 * (3 * 1 - 2);
}

// REPEAT 2 - TIME: 3.3525206 s

method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(2);
expect r0 == 2 * (3 * 2 - 2);
}

// REPEAT 3 - TIME: 4.18539 s

method {:test} Test3() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(3);
expect r0 == 3 * (3 * 3 - 2);
}

// REPEAT 4 - TIME: 5.1141439 s

method {:test} Test4() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(4);
expect r0 == 4 * (3 * 4 - 2);
}

// REPEAT 5 - TIME: 5.9429238 s

method {:test} Test5() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(5);
expect r0 == 5 * (3 * 5 - 2);
}

// REPEAT 6 - TIME: 6.6910892 s

method {:test} Test6() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(6);
expect r0 == 6 * (3 * 6 - 2);
}

// REPEAT 7 - TIME: 7.2346727 s

method {:test} Test7() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(7);
expect r0 == 7 * (3 * 7 - 2);
}

// REPEAT 8 - TIME: 7.7179532 s

method {:test} Test8() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(8);
expect r0 == 8 * (3 * 8 - 2);
}

// REPEAT 9 - TIME: 8.2067831 s

method {:test} Test9() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(9);
expect r0 == 9 * (3 * 9 - 2);
}

// REPEAT 10 - TIME: 8.7508675 s
