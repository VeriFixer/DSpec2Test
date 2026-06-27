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

method {:test} Test6() {
var r0, r1 := SwapArithmetic(6, 6);
expect r0 == 6;
expect r1 == 6;
}

// REPEAT 7 - TIME: 6.8333336 s
