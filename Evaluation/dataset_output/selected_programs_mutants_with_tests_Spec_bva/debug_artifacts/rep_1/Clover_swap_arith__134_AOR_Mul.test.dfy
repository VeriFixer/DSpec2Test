// Clover_swap_arith.dfy

method {:testEntry} SwapArithmetic(X: int, Y: int)
    returns (x: int, y: int)
  ensures x == Y
  ensures y == X
{
  x, y := X, Y;
  x := y * x;
  y := y - x;
  x := y + x;
}

method {:test} Test0() {
var r0, r1 := SwapArithmetic(25, 24);
expect r0 == 24;
expect r1 == 25;
}
method {:test} Test1() {
var r0, r1 := SwapArithmetic(-100, 24);
expect r0 == 24;
expect r1 == -100;
}
method {:test} Test2() {
var r0, r1 := SwapArithmetic(100, 24);
expect r0 == 24;
expect r1 == 100;
}
method {:test} Test3() {
var r0, r1 := SwapArithmetic(24, -100);
expect r0 == -100;
expect r1 == 24;
}
method {:test} Test4() {
var r0, r1 := SwapArithmetic(24, 100);
expect r0 == 100;
expect r1 == 24;
}

// REPEAT 1 - TIME: 8.9522746 s
