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

method {:test} Test1() {
var r0, r1 := SwapArithmetic(1, 1);
expect r0 == 1;
expect r1 == 1;
}

// REPEAT 2 - TIME: 4.1972773 s
