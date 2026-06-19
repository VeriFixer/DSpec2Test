// dafny-synthesis_task_id_135.dfy

method {:testEntry} NthHexagonalNumber(n: int) returns (hexNum: int)
  requires n >= 0
  ensures hexNum == n * (2 * n - 1)
{
  hexNum := n * 1;
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(0);
expect r0 == 0 * (2 * 0 - 1);
}

// REPEAT 1 - TIME: 2.5655464 s

method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(1);
expect r0 == 1 * (2 * 1 - 1);
}

// REPEAT 2 - TIME: 3.403422 s

method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(2);
expect r0 == 2 * (2 * 2 - 1);
}

// REPEAT 3 - TIME: 4.2097437 s

method {:test} Test3() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(3);
expect r0 == 3 * (2 * 3 - 1);
}

// REPEAT 4 - TIME: 5.0185055 s

method {:test} Test4() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(4);
expect r0 == 4 * (2 * 4 - 1);
}

// REPEAT 5 - TIME: 5.8111105 s

method {:test} Test5() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(5);
expect r0 == 5 * (2 * 5 - 1);
}

// REPEAT 6 - TIME: 6.6927535 s

method {:test} Test6() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(6);
expect r0 == 6 * (2 * 6 - 1);
}

// REPEAT 7 - TIME: 7.6556543 s

method {:test} Test7() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(7);
expect r0 == 7 * (2 * 7 - 1);
}

// REPEAT 8 - TIME: 8.3109052 s

method {:test} Test8() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(8);
expect r0 == 8 * (2 * 8 - 1);
}

// REPEAT 9 - TIME: 8.9829917 s

method {:test} Test9() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(9);
expect r0 == 9 * (2 * 9 - 1);
}

// REPEAT 10 - TIME: 9.6262142 s
