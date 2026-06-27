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

// REPEAT 1 - TIME: 3.0294857 s
