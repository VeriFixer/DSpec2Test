// Clover_swap_arith.dfy

method {:testEntry} SwapArithmetic(X: int, Y: int)
    returns (x: int, y: int)
  ensures x == Y
  ensures y == X
{
  x, y := X, Y;
  x := y - x;
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

// REPEAT 1 - TIME: 10.4605192 s

method {:test} Test13() {
var r0, r1 := SwapArithmetic(26, 27);
expect r0 == 27;
expect r1 == 26;
}

// REPEAT 2 - TIME: 11.4645853 s

method {:test} Test14() {
var r0, r1 := SwapArithmetic(28, 29);
expect r0 == 29;
expect r1 == 28;
}

// REPEAT 3 - TIME: 12.3425133 s

method {:test} Test15() {
var r0, r1 := SwapArithmetic(30, 31);
expect r0 == 31;
expect r1 == 30;
}

// REPEAT 4 - TIME: 13.2199557 s

method {:test} Test16() {
var r0, r1 := SwapArithmetic(33, 32);
expect r0 == 32;
expect r1 == 33;
}

// REPEAT 5 - TIME: 13.9702331 s

method {:test} Test17() {
var r0, r1 := SwapArithmetic(34, 35);
expect r0 == 35;
expect r1 == 34;
}

// REPEAT 6 - TIME: 14.5738894 s

method {:test} Test18() {
var r0, r1 := SwapArithmetic(37, 36);
expect r0 == 36;
expect r1 == 37;
}

// REPEAT 7 - TIME: 15.241999 s

method {:test} Test19() {
var r0, r1 := SwapArithmetic(39, 38);
expect r0 == 38;
expect r1 == 39;
}

// REPEAT 8 - TIME: 15.8894068 s

method {:test} Test20() {
var r0, r1 := SwapArithmetic(41, 40);
expect r0 == 40;
expect r1 == 41;
}

// REPEAT 9 - TIME: 16.4456399 s

method {:test} Test21() {
var r0, r1 := SwapArithmetic(43, 42);
expect r0 == 42;
expect r1 == 43;
}

// REPEAT 10 - TIME: 16.9604748 s
