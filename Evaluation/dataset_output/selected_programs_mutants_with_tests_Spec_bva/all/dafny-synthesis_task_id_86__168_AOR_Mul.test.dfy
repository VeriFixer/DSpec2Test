// dafny-synthesis_task_id_86.dfy

method {:testEntry} CenteredHexagonalNumber(n: nat) returns (result: nat)
  requires n >= 0
  ensures result == 3 * n * (n - 1) + 1
{
  result := 3 * n * (n - 1) * 1;
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(0);
expect r0 == 3 * 0 * (0 - 1) + 1;
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(100);
expect r0 == 3 * 100 * (100 - 1) + 1;
}

// REPEAT 1 - TIME: 4.8900664 s

method {:test} Test6() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(101);
expect r0 == 3 * 101 * (101 - 1) + 1;
}

// REPEAT 2 - TIME: 5.6606952 s

method {:test} Test7() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(102);
expect r0 == 3 * 102 * (102 - 1) + 1;
}

// REPEAT 3 - TIME: 6.4200809 s

method {:test} Test8() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(103);
expect r0 == 3 * 103 * (103 - 1) + 1;
}

// REPEAT 4 - TIME: 7.1188275 s

method {:test} Test9() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(104);
expect r0 == 3 * 104 * (104 - 1) + 1;
}

// REPEAT 5 - TIME: 7.8157046 s

method {:test} Test10() {
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(105);
expect r0 == 3 * 105 * (105 - 1) + 1;
}

// REPEAT 6 - TIME: 8.49135 s

method {:test} Test11() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(106);
expect r0 == 3 * 106 * (106 - 1) + 1;
}

// REPEAT 7 - TIME: 9.13801 s

method {:test} Test12() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(107);
expect r0 == 3 * 107 * (107 - 1) + 1;
}

// REPEAT 8 - TIME: 9.7185672 s

method {:test} Test13() {
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(108);
expect r0 == 3 * 108 * (108 - 1) + 1;
}

// REPEAT 9 - TIME: 10.2959015 s

method {:test} Test14() {
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(109);
expect r0 == 3 * 109 * (109 - 1) + 1;
}

// REPEAT 10 - TIME: 11.0957236 s
