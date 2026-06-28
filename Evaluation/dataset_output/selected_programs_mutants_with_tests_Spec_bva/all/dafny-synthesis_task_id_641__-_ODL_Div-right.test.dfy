// dafny-synthesis_task_id_641.dfy

method {:testEntry} NthNonagonalNumber(n: int) returns (number: int)
  requires n >= 0
  ensures number == n * (7 * n - 5) / 2
{
  number := n * (7 * n - 5);
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(0);
expect r0 == 0 * (7 * 0 - 5) / 2;
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(100);
expect r0 == 100 * (7 * 100 - 5) / 2;
}

// REPEAT 1 - TIME: 37.791543 s

method {:test} Test6() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(101);
expect r0 == 101 * (7 * 101 - 5) / 2;
}

// REPEAT 2 - TIME: 38.951892 s

method {:test} Test7() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(102);
expect r0 == 102 * (7 * 102 - 5) / 2;
}

// REPEAT 3 - TIME: 40.0647057 s

method {:test} Test8() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(103);
expect r0 == 103 * (7 * 103 - 5) / 2;
}

// REPEAT 4 - TIME: 40.9906632 s

method {:test} Test9() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(104);
expect r0 == 104 * (7 * 104 - 5) / 2;
}

// REPEAT 5 - TIME: 42.0264095 s

method {:test} Test10() {
expect 341796877 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(341796877);
expect r0 == 341796877 * (7 * 341796877 - 5) / 2;
}

// REPEAT 6 - TIME: 42.8464495 s

method {:test} Test11() {
expect 341796878 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(341796878);
expect r0 == 341796878 * (7 * 341796878 - 5) / 2;
}

// REPEAT 7 - TIME: 43.7432568 s

method {:test} Test12() {
expect 163555288339858862 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(163555288339858862);
expect r0 == 163555288339858862 * (7 * 163555288339858862 - 5) / 2;
}

// REPEAT 8 - TIME: 45.0250624 s

method {:test} Test13() {
expect 37450465281508189576483680376842269 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(37450465281508189576483680376842269);
expect r0 == 37450465281508189576483680376842269 * (7 * 37450465281508189576483680376842269 - 5) / 2;
}

// REPEAT 9 - TIME: 49.5442758 s

method {:test} Test14() {
expect 37450465281508189576483680376842270 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(37450465281508189576483680376842270);
expect r0 == 37450465281508189576483680376842270 * (7 * 37450465281508189576483680376842270 - 5) / 2;
}

// REPEAT 10 - TIME: 50.3922843 s
