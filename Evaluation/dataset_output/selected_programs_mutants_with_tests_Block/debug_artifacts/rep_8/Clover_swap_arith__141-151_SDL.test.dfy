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

method {:test} Test7() {
var r0, r1 := SwapArithmetic(7, 7);
expect r0 == 7;
expect r1 == 7;
}

// REPEAT 8 - TIME: 6.1514767 s
