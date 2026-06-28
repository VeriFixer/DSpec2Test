// Clover_swap_arith.dfy

method {:testEntry} SwapArithmetic(X: int, Y: int)
    returns (x: int, y: int)
  ensures x == Y
  ensures y == X
{
  x, y := X, Y;
  x := y - x;
  y := y + x;
  x := y + x;
}


method {:test} Test0() {
var r0, r1 := SwapArithmetic(0, 0);
expect r0 == 0;
expect r1 == 0;
}

// REPEAT 1 - TIME: 1.7509558 s

method {:test} Test1() {
var r0, r1 := SwapArithmetic(1, 1);
expect r0 == 1;
expect r1 == 1;
}

// REPEAT 2 - TIME: 2.2716764 s

method {:test} Test2() {
var r0, r1 := SwapArithmetic(2, 2);
expect r0 == 2;
expect r1 == 2;
}

// REPEAT 3 - TIME: 2.8804966 s

method {:test} Test3() {
var r0, r1 := SwapArithmetic(3, 3);
expect r0 == 3;
expect r1 == 3;
}

// REPEAT 4 - TIME: 3.5508812 s

method {:test} Test4() {
var r0, r1 := SwapArithmetic(4, 4);
expect r0 == 4;
expect r1 == 4;
}

// REPEAT 5 - TIME: 4.1854062 s

method {:test} Test5() {
var r0, r1 := SwapArithmetic(5, 5);
expect r0 == 5;
expect r1 == 5;
}

// REPEAT 6 - TIME: 4.8250866 s

method {:test} Test6() {
var r0, r1 := SwapArithmetic(6, 6);
expect r0 == 6;
expect r1 == 6;
}

// REPEAT 7 - TIME: 5.3069375 s

method {:test} Test7() {
var r0, r1 := SwapArithmetic(7, 7);
expect r0 == 7;
expect r1 == 7;
}

// REPEAT 8 - TIME: 6.1514767 s

method {:test} Test8() {
var r0, r1 := SwapArithmetic(8, 8);
expect r0 == 8;
expect r1 == 8;
}

// REPEAT 9 - TIME: 6.7083722 s

method {:test} Test9() {
var r0, r1 := SwapArithmetic(9, 9);
expect r0 == 9;
expect r1 == 9;
}

// REPEAT 10 - TIME: 7.269807 s
