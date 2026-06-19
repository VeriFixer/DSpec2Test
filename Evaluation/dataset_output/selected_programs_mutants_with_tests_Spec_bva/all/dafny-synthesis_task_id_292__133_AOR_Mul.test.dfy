// dafny-synthesis_task_id_292.dfy

method {:testEntry} Quotient(a: int, b: int) returns (result: int)
  requires b != 0
  ensures result == a / b
{
  result := a * b;
}


method {:test} Test0() {
expect -1 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(-8365, -1);
expect r0 == -8365 / -1;
}
method {:test} Test1() {
expect -1 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(-100, -1);
expect r0 == -100 / -1;
}
method {:test} Test2() {
expect -1 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(100, -1);
expect r0 == 100 / -1;
}
method {:test} Test3() {
expect -100 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(-771900, -100);
expect r0 == -771900 / -100;
}
method {:test} Test4() {
expect 100 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(771900, 100);
expect r0 == 771900 / 100;
}
method {:test} Test5() {
expect -1 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(1236, -1);
expect r0 == 1236 / -1;
}
method {:test} Test8() {
expect -1 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(7719, -1);
expect r0 == 7719 / -1;
}

// REPEAT 1 - TIME: 6.946246 s

method {:test} Test10() {
expect -99 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(771902, -99);
expect r0 == 771902 / -99;
}

// REPEAT 2 - TIME: 7.8132481 s

method {:test} Test11() {
expect -98 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(771945, -98);
expect r0 == 771945 / -98;
}

// REPEAT 3 - TIME: 8.5050991 s

method {:test} Test12() {
expect -97 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(772022, -97);
expect r0 == 772022 / -97;
}

// REPEAT 4 - TIME: 9.206849 s

method {:test} Test13() {
expect -96 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(772031, -96);
expect r0 == 772031 / -96;
}

// REPEAT 5 - TIME: 9.935179 s

method {:test} Test14() {
expect -95 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(772064, -95);
expect r0 == 772064 / -95;
}

// REPEAT 6 - TIME: 10.7223734 s

method {:test} Test15() {
expect -94 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(772115, -94);
expect r0 == 772115 / -94;
}

// REPEAT 7 - TIME: 11.3316272 s

method {:test} Test16() {
expect -93 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(772178, -93);
expect r0 == 772178 / -93;
}

// REPEAT 8 - TIME: 12.0358413 s

method {:test} Test17() {
expect -92 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(772247, -92);
expect r0 == 772247 / -92;
}

// REPEAT 9 - TIME: 12.7664338 s

method {:test} Test18() {
expect -91 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(772316, -91);
expect r0 == 772316 / -91;
}

// REPEAT 10 - TIME: 13.299913 s
