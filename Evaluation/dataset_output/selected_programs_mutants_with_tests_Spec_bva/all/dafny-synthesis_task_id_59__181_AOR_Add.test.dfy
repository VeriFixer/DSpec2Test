// dafny-synthesis_task_id_59.dfy

method {:testEntry} NthOctagonalNumber(n: int) returns (octagonalNumber: int)
  requires n >= 0
  ensures octagonalNumber == n * (3 * n - 2)
{
  octagonalNumber := n * (3 * n + 2);
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(0);
expect r0 == 0 * (3 * 0 - 2);
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(100);
expect r0 == 100 * (3 * 100 - 2);
}

// REPEAT 1 - TIME: 5.7265745 s

method {:test} Test6() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(101);
expect r0 == 101 * (3 * 101 - 2);
}

// REPEAT 2 - TIME: 6.5524481 s

method {:test} Test7() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(102);
expect r0 == 102 * (3 * 102 - 2);
}

// REPEAT 3 - TIME: 7.3496735 s

method {:test} Test8() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(103);
expect r0 == 103 * (3 * 103 - 2);
}

// REPEAT 4 - TIME: 8.0837064 s

method {:test} Test9() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(104);
expect r0 == 104 * (3 * 104 - 2);
}

// REPEAT 5 - TIME: 8.7712287 s

method {:test} Test10() {
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(105);
expect r0 == 105 * (3 * 105 - 2);
}

// REPEAT 6 - TIME: 9.3731328 s

method {:test} Test11() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(106);
expect r0 == 106 * (3 * 106 - 2);
}

// REPEAT 7 - TIME: 10.1304428 s

method {:test} Test12() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(107);
expect r0 == 107 * (3 * 107 - 2);
}

// REPEAT 8 - TIME: 10.7888184 s

method {:test} Test13() {
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(108);
expect r0 == 108 * (3 * 108 - 2);
}

// REPEAT 9 - TIME: 11.5023196 s

method {:test} Test14() {
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(109);
expect r0 == 109 * (3 * 109 - 2);
}

// REPEAT 10 - TIME: 12.2595377 s
