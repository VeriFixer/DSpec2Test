// dafny-synthesis_task_id_404.dfy

method {:testEntry} Min(a: int, b: int) returns (minValue: int)
  ensures minValue == a || minValue == b
  ensures minValue <= a && minValue <= b
{
  if a == b {
    minValue := a;
  } else {
    minValue := b;
  }
}

method {:test} Test0() {
var r0 := Min(0, 0);
expect r0 == 0 || r0 == 0;
expect r0 <= 0 && r0 <= 0;
}
method {:test} Test1() {
var r0 := Min(-100, 0);
expect r0 == -100 || r0 == 0;
expect r0 <= -100 && r0 <= 0;
}
method {:test} Test2() {
var r0 := Min(100, 100);
expect r0 == 100 || r0 == 100;
expect r0 <= 100 && r0 <= 100;
}
method {:test} Test3() {
var r0 := Min(-100, -100);
expect r0 == -100 || r0 == -100;
expect r0 <= -100 && r0 <= -100;
}
method {:test} Test4() {
var r0 := Min(0, 100);
expect r0 == 0 || r0 == 100;
expect r0 <= 0 && r0 <= 100;
}
method {:test} Test10() {
var r0 := Min(1, 0);
expect r0 == 1 || r0 == 0;
expect r0 <= 1 && r0 <= 0;
}
method {:test} Test11() {
var r0 := Min(-100, -101);
expect r0 == -100 || r0 == -101;
expect r0 <= -100 && r0 <= -101;
}
method {:test} Test12() {
var r0 := Min(100, 0);
expect r0 == 100 || r0 == 0;
expect r0 <= 100 && r0 <= 0;
}
method {:test} Test13() {
var r0 := Min(0, -100);
expect r0 == 0 || r0 == -100;
expect r0 <= 0 && r0 <= -100;
}
method {:test} Test14() {
var r0 := Min(101, 100);
expect r0 == 101 || r0 == 100;
expect r0 <= 101 && r0 <= 100;
}

// REPEAT 1 - TIME: 10.58828 s
