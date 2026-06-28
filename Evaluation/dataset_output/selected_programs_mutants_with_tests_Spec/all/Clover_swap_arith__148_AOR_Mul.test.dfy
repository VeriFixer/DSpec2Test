// Clover_swap_arith.dfy

method {:testEntry} SwapArithmetic(X: int, Y: int)
    returns (x: int, y: int)
  ensures x == Y
  ensures y == X
{
  x, y := X, Y;
  x := y - x;
  y := y * x;
  x := y + x;
}


method {:test} Test0() {
var r0, r1 := SwapArithmetic(25, 24);
expect r0 == 24;
expect r1 == 25;
}

// REPEAT 1 - TIME: 2.7819157 s

method {:test} Test1() {
var r0, r1 := SwapArithmetic(26, 27);
expect r0 == 27;
expect r1 == 26;
}

// REPEAT 2 - TIME: 3.806163 s

method {:test} Test2() {
var r0, r1 := SwapArithmetic(29, 28);
expect r0 == 28;
expect r1 == 29;
}

// REPEAT 3 - TIME: 4.8316262 s

method {:test} Test3() {
var r0, r1 := SwapArithmetic(31, 30);
expect r0 == 30;
expect r1 == 31;
}

// REPEAT 4 - TIME: 5.7373461 s

method {:test} Test4() {
var r0, r1 := SwapArithmetic(33, 32);
expect r0 == 32;
expect r1 == 33;
}

// REPEAT 5 - TIME: 6.8186684 s

method {:test} Test5() {
var r0, r1 := SwapArithmetic(35, 34);
expect r0 == 34;
expect r1 == 35;
}

// REPEAT 6 - TIME: 7.9476923 s

method {:test} Test6() {
var r0, r1 := SwapArithmetic(37, 36);
expect r0 == 36;
expect r1 == 37;
}

// REPEAT 7 - TIME: 8.7930307 s

method {:test} Test7() {
var r0, r1 := SwapArithmetic(39, 38);
expect r0 == 38;
expect r1 == 39;
}

// REPEAT 8 - TIME: 9.5855823 s

method {:test} Test8() {
var r0, r1 := SwapArithmetic(41, 40);
expect r0 == 40;
expect r1 == 41;
}

// REPEAT 9 - TIME: 10.2561334 s

method {:test} Test9() {
var r0, r1 := SwapArithmetic(42, 43);
expect r0 == 43;
expect r1 == 42;
}

// REPEAT 10 - TIME: 10.9521311 s
