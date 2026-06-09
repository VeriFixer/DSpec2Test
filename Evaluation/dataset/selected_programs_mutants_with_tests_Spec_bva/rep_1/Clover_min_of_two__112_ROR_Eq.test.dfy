// Clover_min_of_two.dfy

method {:testEntry} Min(x: int, y: int) returns (z: int)
  ensures x <= y ==> z == x
  ensures x > y ==> z == y
{
  if x == y {
    return x;
  } else {
    return y;
  }
}

method {:test} Test0() {
var r0 := Min(1, 0);
expect 1 <= 0 ==> r0 == 1;
expect 1 > 0 ==> r0 == 0;
}
method {:test} Test1() {
var r0 := Min(-100, -101);
expect -100 <= -101 ==> r0 == -100;
expect -100 > -101 ==> r0 == -101;
}
method {:test} Test2() {
var r0 := Min(100, 0);
expect 100 <= 0 ==> r0 == 100;
expect 100 > 0 ==> r0 == 0;
}
method {:test} Test3() {
var r0 := Min(0, -100);
expect 0 <= -100 ==> r0 == 0;
expect 0 > -100 ==> r0 == -100;
}
method {:test} Test4() {
var r0 := Min(101, 100);
expect 101 <= 100 ==> r0 == 101;
expect 101 > 100 ==> r0 == 100;
}
method {:test} Test10() {
var r0 := Min(0, 0);
expect 0 <= 0 ==> r0 == 0;
expect 0 > 0 ==> r0 == 0;
}
method {:test} Test11() {
var r0 := Min(-100, 0);
expect -100 <= 0 ==> r0 == -100;
expect -100 > 0 ==> r0 == 0;
}
method {:test} Test12() {
var r0 := Min(100, 100);
expect 100 <= 100 ==> r0 == 100;
expect 100 > 100 ==> r0 == 100;
}
method {:test} Test13() {
var r0 := Min(-100, -100);
expect -100 <= -100 ==> r0 == -100;
expect -100 > -100 ==> r0 == -100;
}
method {:test} Test14() {
var r0 := Min(0, 100);
expect 0 <= 100 ==> r0 == 0;
expect 0 > 100 ==> r0 == 100;
}

// REPEAT 1 - TIME: 13.3897251 s
