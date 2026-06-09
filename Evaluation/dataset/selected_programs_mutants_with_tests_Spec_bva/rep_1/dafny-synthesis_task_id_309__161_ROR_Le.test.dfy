// dafny-synthesis_task_id_309.dfy

method {:testEntry} Max(a: int, b: int) returns (maxValue: int)
  ensures maxValue == a || maxValue == b
  ensures maxValue >= a && maxValue >= b
{
  if a <= b {
    maxValue := a;
  } else {
    maxValue := b;
  }
}

method {:test} Test0() {
var r0 := Max(0, 0);
expect r0 == 0 || r0 == 0;
expect r0 >= 0 && r0 >= 0;
}
method {:test} Test1() {
var r0 := Max(-100, -100);
expect r0 == -100 || r0 == -100;
expect r0 >= -100 && r0 >= -100;
}
method {:test} Test2() {
var r0 := Max(100, 0);
expect r0 == 100 || r0 == 0;
expect r0 >= 100 && r0 >= 0;
}
method {:test} Test3() {
var r0 := Max(0, -100);
expect r0 == 0 || r0 == -100;
expect r0 >= 0 && r0 >= -100;
}
method {:test} Test4() {
var r0 := Max(100, 100);
expect r0 == 100 || r0 == 100;
expect r0 >= 100 && r0 >= 100;
}
method {:test} Test10() {
var r0 := Max(-1, 0);
expect r0 == -1 || r0 == 0;
expect r0 >= -1 && r0 >= 0;
}
method {:test} Test11() {
var r0 := Max(-100, 0);
expect r0 == -100 || r0 == 0;
expect r0 >= -100 && r0 >= 0;
}
method {:test} Test12() {
var r0 := Max(100, 101);
expect r0 == 100 || r0 == 101;
expect r0 >= 100 && r0 >= 101;
}
method {:test} Test13() {
var r0 := Max(-101, -100);
expect r0 == -101 || r0 == -100;
expect r0 >= -101 && r0 >= -100;
}
method {:test} Test14() {
var r0 := Max(0, 100);
expect r0 == 0 || r0 == 100;
expect r0 >= 0 && r0 >= 100;
}

// REPEAT 1 - TIME: 9.2670266 s
