// dafny-synthesis_task_id_135.dfy

method {:testEntry} NthHexagonalNumber(n: int) returns (hexNum: int)
  requires n >= 0
  ensures hexNum == n * (2 * n - 1)
{
  hexNum := n * (2 * n);
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(0);
expect r0 == 0 * (2 * 0 - 1);
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(100);
expect r0 == 100 * (2 * 100 - 1);
}

// REPEAT 1 - TIME: 6.8728343 s

method {:test} Test6() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(101);
expect r0 == 101 * (2 * 101 - 1);
}

// REPEAT 2 - TIME: 8.3359275 s

method {:test} Test7() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(102);
expect r0 == 102 * (2 * 102 - 1);
}

// REPEAT 3 - TIME: 9.5722638 s

method {:test} Test8() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(103);
expect r0 == 103 * (2 * 103 - 1);
}

// REPEAT 4 - TIME: 10.7947281 s

method {:test} Test9() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(104);
expect r0 == 104 * (2 * 104 - 1);
}

// REPEAT 5 - TIME: 11.6937689 s

method {:test} Test10() {
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(105);
expect r0 == 105 * (2 * 105 - 1);
}

// REPEAT 6 - TIME: 12.5007683 s

method {:test} Test11() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(106);
expect r0 == 106 * (2 * 106 - 1);
}

// REPEAT 7 - TIME: 13.4041805 s

method {:test} Test12() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(107);
expect r0 == 107 * (2 * 107 - 1);
}

// REPEAT 8 - TIME: 14.1714528 s

method {:test} Test13() {
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(108);
expect r0 == 108 * (2 * 108 - 1);
}

// REPEAT 9 - TIME: 15.0840247 s

method {:test} Test14() {
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(109);
expect r0 == 109 * (2 * 109 - 1);
}

// REPEAT 10 - TIME: 15.9510508 s
