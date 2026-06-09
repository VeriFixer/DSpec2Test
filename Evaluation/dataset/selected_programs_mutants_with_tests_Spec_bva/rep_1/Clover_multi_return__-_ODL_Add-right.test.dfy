// Clover_multi_return.dfy

method {:testEntry} MultipleReturns(x: int, y: int)
    returns (more: int, less: int)
  ensures more == x + y
  ensures less == x - y
{
  more := x;
  less := x - y;
}

method {:test} Test0() {
var r0, r1 := MultipleReturns(0, 0);
expect r0 == 0 + 0;
expect r1 == 0 - 0;
}
method {:test} Test1() {
var r0, r1 := MultipleReturns(-100, 0);
expect r0 == -100 + 0;
expect r1 == -100 - 0;
}
method {:test} Test2() {
var r0, r1 := MultipleReturns(100, 0);
expect r0 == 100 + 0;
expect r1 == 100 - 0;
}
method {:test} Test3() {
var r0, r1 := MultipleReturns(0, -100);
expect r0 == 0 + -100;
expect r1 == 0 - -100;
}
method {:test} Test4() {
var r0, r1 := MultipleReturns(0, 100);
expect r0 == 0 + 100;
expect r1 == 0 - 100;
}

// REPEAT 1 - TIME: 6.8200063 s
