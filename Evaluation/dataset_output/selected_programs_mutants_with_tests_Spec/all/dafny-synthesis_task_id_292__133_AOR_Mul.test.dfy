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

// REPEAT 1 - TIME: 2.5899203 s

method {:test} Test1() {
expect -2 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(-8364, -2);
expect r0 == -8364 / -2;
}

// REPEAT 2 - TIME: 3.5702417 s

method {:test} Test2() {
expect -3 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(-8361, -3);
expect r0 == -8361 / -3;
}

// REPEAT 3 - TIME: 4.6266307 s

method {:test} Test3() {
expect -4 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(-8360, -4);
expect r0 == -8360 / -4;
}

// REPEAT 4 - TIME: 5.6401791 s

method {:test} Test4() {
expect -5 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(-8355, -5);
expect r0 == -8355 / -5;
}

// REPEAT 5 - TIME: 6.5502742 s

method {:test} Test5() {
expect -6 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(-8352, -6);
expect r0 == -8352 / -6;
}

// REPEAT 6 - TIME: 7.5986294 s

method {:test} Test6() {
expect -7 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(0, -7);
expect r0 == 0 / -7;
}

// REPEAT 7 - TIME: 8.3669211 s

method {:test} Test7() {
expect -8 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(8, -8);
expect r0 == 8 / -8;
}

// REPEAT 8 - TIME: 9.0266596 s

method {:test} Test8() {
expect -9 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(9, -9);
expect r0 == 9 / -9;
}

// REPEAT 9 - TIME: 9.596386 s

method {:test} Test9() {
expect -10 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(10, -10);
expect r0 == 10 / -10;
}

// REPEAT 10 - TIME: 10.2347519 s
