// dafny-synthesis_task_id_641.dfy

method {:testEntry} NthNonagonalNumber(n: int) returns (number: int)
  requires n >= 0
  ensures number == n * (7 * n - 5) / 2
{
  number := (n - (7 * n - 5)) / 2;
}


method {:testEntry} NthNonagonalNumber(n: int) returns (number: int)
    requires n >= 0
    ensures number == n * (7 * n - 5) / 2
{
    number := n * (7 * n - 5) / 2;
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

// REPEAT 1 - TIME: 35.4435205 s

method {:test} Test6() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(101);
expect r0 == 101 * (7 * 101 - 5) / 2;
}

// REPEAT 2 - TIME: 36.345439 s

method {:test} Test7() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(102);
expect r0 == 102 * (7 * 102 - 5) / 2;
}

// REPEAT 3 - TIME: 36.9933104 s

method {:test} Test8() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(103);
expect r0 == 103 * (7 * 103 - 5) / 2;
}

// REPEAT 4 - TIME: 37.6226995 s

method {:test} Test9() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(104);
expect r0 == 104 * (7 * 104 - 5) / 2;
}

// REPEAT 5 - TIME: 38.4409564 s

method {:test} Test10() {
expect 341796877 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(341796877);
expect r0 == 341796877 * (7 * 341796877 - 5) / 2;
}

// REPEAT 6 - TIME: 39.1196512 s

method {:test} Test11() {
expect 341796878 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(341796878);
expect r0 == 341796878 * (7 * 341796878 - 5) / 2;
}

// REPEAT 7 - TIME: 39.7665657 s

method {:test} Test12() {
expect 163555288339858862 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(163555288339858862);
expect r0 == 163555288339858862 * (7 * 163555288339858862 - 5) / 2;
}

// REPEAT 8 - TIME: 40.6339259 s

method {:test} Test13() {
expect 37450465281508189576483680376842269 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(37450465281508189576483680376842269);
expect r0 == 37450465281508189576483680376842269 * (7 * 37450465281508189576483680376842269 - 5) / 2;
}

// REPEAT 9 - TIME: 44.0101685 s

method {:test} Test14() {
expect 37450465281508189576483680376842270 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(37450465281508189576483680376842270);
expect r0 == 37450465281508189576483680376842270 * (7 * 37450465281508189576483680376842270 - 5) / 2;
}

// REPEAT 10 - TIME: 44.5345843 s
