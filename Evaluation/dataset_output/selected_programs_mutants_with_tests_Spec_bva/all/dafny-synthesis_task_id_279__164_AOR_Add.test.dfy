// dafny-synthesis_task_id_279.dfy

method {:testEntry} NthDecagonalNumber(n: int) returns (decagonal: int)
  requires n >= 0
  ensures decagonal == 4 * n * n - 3 * n
{
  decagonal := 4 * n * n + 3 * n;
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(0);
expect r0 == 4 * 0 * 0 - 3 * 0;
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(100);
expect r0 == 4 * 100 * 100 - 3 * 100;
}

// REPEAT 1 - TIME: 5.1088906 s

method {:test} Test6() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(101);
expect r0 == 4 * 101 * 101 - 3 * 101;
}

// REPEAT 2 - TIME: 6.1146846 s

method {:test} Test7() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(102);
expect r0 == 4 * 102 * 102 - 3 * 102;
}

// REPEAT 3 - TIME: 7.0919423 s

method {:test} Test8() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(103);
expect r0 == 4 * 103 * 103 - 3 * 103;
}

// REPEAT 4 - TIME: 7.7571749 s

method {:test} Test9() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(104);
expect r0 == 4 * 104 * 104 - 3 * 104;
}

// REPEAT 5 - TIME: 8.5327807 s

method {:test} Test10() {
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(105);
expect r0 == 4 * 105 * 105 - 3 * 105;
}

// REPEAT 6 - TIME: 9.2684703 s

method {:test} Test11() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(106);
expect r0 == 4 * 106 * 106 - 3 * 106;
}

// REPEAT 7 - TIME: 10.260653 s

method {:test} Test12() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(107);
expect r0 == 4 * 107 * 107 - 3 * 107;
}

// REPEAT 8 - TIME: 10.9727032 s

method {:test} Test13() {
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(108);
expect r0 == 4 * 108 * 108 - 3 * 108;
}

// REPEAT 9 - TIME: 11.7915971 s

method {:test} Test14() {
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(109);
expect r0 == 4 * 109 * 109 - 3 * 109;
}

// REPEAT 10 - TIME: 12.6659571 s
