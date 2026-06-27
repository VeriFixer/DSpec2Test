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

method {:test} Test4() {
var r0, r1 := SwapArithmetic(4, 4);
expect r0 == 4;
expect r1 == 4;
}

// REPEAT 5 - TIME: 4.7784408 s
