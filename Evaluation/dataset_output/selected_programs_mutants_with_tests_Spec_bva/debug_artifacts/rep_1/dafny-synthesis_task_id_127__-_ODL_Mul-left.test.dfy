// dafny-synthesis_task_id_127.dfy

method {:testEntry} Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := b;
}

method {:test} Test0() {
var r0 := Multiply(7719, 0);
expect r0 == 7719 * 0;
}
method {:test} Test1() {
var r0 := Multiply(-100, 0);
expect r0 == -100 * 0;
}
method {:test} Test2() {
var r0 := Multiply(100, 0);
expect r0 == 100 * 0;
}
method {:test} Test3() {
var r0 := Multiply(0, -100);
expect r0 == 0 * -100;
}
method {:test} Test4() {
var r0 := Multiply(0, 100);
expect r0 == 0 * 100;
}
method {:test} Test6() {
var r0 := Multiply(-100, 1);
expect r0 == -100 * 1;
}
method {:test} Test7() {
var r0 := Multiply(100, 1);
expect r0 == 100 * 1;
}

// REPEAT 1 - TIME: 9.1348516 s
