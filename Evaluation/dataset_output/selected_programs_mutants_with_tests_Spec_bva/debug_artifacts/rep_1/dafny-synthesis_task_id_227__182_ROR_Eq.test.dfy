// dafny-synthesis_task_id_227.dfy

method {:testEntry} MinOfThree(a: int, b: int, c: int)
    returns (min: int)
  ensures min <= a && min <= b && min <= c
  ensures min == a || min == b || min == c
{
  if a == b && a <= c {
    min := a;
  } else if b <= a && b <= c {
    min := b;
  } else {
    min := c;
  }
}

method {:test} Test0() {
var r0 := MinOfThree(0, 0, 0);
expect r0 <= 0 && r0 <= 0 && r0 <= 0;
expect r0 == 0 || r0 == 0 || r0 == 0;
}
method {:test} Test1() {
var r0 := MinOfThree(-100, 0, 0);
expect r0 <= -100 && r0 <= 0 && r0 <= 0;
expect r0 == -100 || r0 == 0 || r0 == 0;
}
method {:test} Test2() {
var r0 := MinOfThree(100, 100, 100);
expect r0 <= 100 && r0 <= 100 && r0 <= 100;
expect r0 == 100 || r0 == 100 || r0 == 100;
}
method {:test} Test3() {
var r0 := MinOfThree(-100, -100, 0);
expect r0 <= -100 && r0 <= -100 && r0 <= 0;
expect r0 == -100 || r0 == -100 || r0 == 0;
}
method {:test} Test4() {
var r0 := MinOfThree(0, 100, 0);
expect r0 <= 0 && r0 <= 100 && r0 <= 0;
expect r0 == 0 || r0 == 100 || r0 == 0;
}
method {:test} Test5() {
var r0 := MinOfThree(-100, 0, -100);
expect r0 <= -100 && r0 <= 0 && r0 <= -100;
expect r0 == -100 || r0 == 0 || r0 == -100;
}
method {:test} Test6() {
var r0 := MinOfThree(0, 0, 100);
expect r0 <= 0 && r0 <= 0 && r0 <= 100;
expect r0 == 0 || r0 == 0 || r0 == 100;
}
method {:test} Test12() {
var r0 := MinOfThree(1, 0, 0);
expect r0 <= 1 && r0 <= 0 && r0 <= 0;
expect r0 == 1 || r0 == 0 || r0 == 0;
}
method {:test} Test13() {
var r0 := MinOfThree(-100, -101, 0);
expect r0 <= -100 && r0 <= -101 && r0 <= 0;
expect r0 == -100 || r0 == -101 || r0 == 0;
}
method {:test} Test14() {
var r0 := MinOfThree(100, 0, 0);
expect r0 <= 100 && r0 <= 0 && r0 <= 0;
expect r0 == 100 || r0 == 0 || r0 == 0;
}
method {:test} Test15() {
var r0 := MinOfThree(0, -100, 0);
expect r0 <= 0 && r0 <= -100 && r0 <= 0;
expect r0 == 0 || r0 == -100 || r0 == 0;
}
method {:test} Test16() {
var r0 := MinOfThree(101, 100, 100);
expect r0 <= 101 && r0 <= 100 && r0 <= 100;
expect r0 == 101 || r0 == 100 || r0 == 100;
}
method {:test} Test17() {
var r0 := MinOfThree(0, -100, -100);
expect r0 <= 0 && r0 <= -100 && r0 <= -100;
expect r0 == 0 || r0 == -100 || r0 == -100;
}
method {:test} Test18() {
var r0 := MinOfThree(1, 0, 100);
expect r0 <= 1 && r0 <= 0 && r0 <= 100;
expect r0 == 1 || r0 == 0 || r0 == 100;
}
method {:test} Test24() {
var r0 := MinOfThree(1, 1, 0);
expect r0 <= 1 && r0 <= 1 && r0 <= 0;
expect r0 == 1 || r0 == 1 || r0 == 0;
}
method {:test} Test25() {
var r0 := MinOfThree(-100, 0, -101);
expect r0 <= -100 && r0 <= 0 && r0 <= -101;
expect r0 == -100 || r0 == 0 || r0 == -101;
}
method {:test} Test26() {
var r0 := MinOfThree(100, 1, 0);
expect r0 <= 100 && r0 <= 1 && r0 <= 0;
expect r0 == 100 || r0 == 1 || r0 == 0;
}
method {:test} Test27() {
var r0 := MinOfThree(0, -100, -101);
expect r0 <= 0 && r0 <= -100 && r0 <= -101;
expect r0 == 0 || r0 == -100 || r0 == -101;
}
method {:test} Test28() {
var r0 := MinOfThree(1, 100, 0);
expect r0 <= 1 && r0 <= 100 && r0 <= 0;
expect r0 == 1 || r0 == 100 || r0 == 0;
}
method {:test} Test29() {
var r0 := MinOfThree(0, 0, -100);
expect r0 <= 0 && r0 <= 0 && r0 <= -100;
expect r0 == 0 || r0 == 0 || r0 == -100;
}
method {:test} Test30() {
var r0 := MinOfThree(101, 101, 100);
expect r0 <= 101 && r0 <= 101 && r0 <= 100;
expect r0 == 101 || r0 == 101 || r0 == 100;
}

// REPEAT 1 - TIME: 21.0182881 s
