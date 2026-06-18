// dafny-synthesis_task_id_292.dfy

method {:testEntry} Quotient(a: int, b: int) returns (result: int)
  requires b != 0
  ensures result == a / b
{
  result := b / b;
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

// REPEAT 1 - TIME: 6.6383091 s
