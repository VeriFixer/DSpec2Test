// dafny-synthesis_task_id_292.dfy

method {:testEntry} Quotient(a: int, b: int) returns (result: int)
  requires b != 0
  ensures result == a / b
{
  result := 0;
}


method {:test} Test0() {
expect -1 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(-8365, -1);
expect r0 == -8365 / -1;
}

// REPEAT 1 - TIME: 2.1788266 s

method {:test} Test1() {
expect -2 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(-8364, -2);
expect r0 == -8364 / -2;
}

// REPEAT 2 - TIME: 2.8963782 s

method {:test} Test2() {
expect -3 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(-8361, -3);
expect r0 == -8361 / -3;
}

// REPEAT 3 - TIME: 3.6612586 s

method {:test} Test3() {
expect -4 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(-8360, -4);
expect r0 == -8360 / -4;
}

// REPEAT 4 - TIME: 4.4259808 s

method {:test} Test4() {
expect -5 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(-8355, -5);
expect r0 == -8355 / -5;
}

// REPEAT 5 - TIME: 5.2112882 s

method {:test} Test5() {
expect -6 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(-8352, -6);
expect r0 == -8352 / -6;
}

// REPEAT 6 - TIME: 6.1601019 s

method {:test} Test6() {
expect -7 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(0, -7);
expect r0 == 0 / -7;
}

// REPEAT 7 - TIME: 6.9295418 s

method {:test} Test7() {
expect -8 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(8, -8);
expect r0 == 8 / -8;
}

// REPEAT 8 - TIME: 7.6853531 s

method {:test} Test8() {
expect -9 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(9, -9);
expect r0 == 9 / -9;
}

// REPEAT 9 - TIME: 8.4764316 s

method {:test} Test9() {
expect -10 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Quotient(10, -10);
expect r0 == 10 / -10;
}

// REPEAT 10 - TIME: 9.0940659 s
