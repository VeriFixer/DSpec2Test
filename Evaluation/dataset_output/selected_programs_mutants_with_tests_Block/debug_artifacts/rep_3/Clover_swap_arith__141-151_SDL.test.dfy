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

method {:test} Test2() {
var r0, r1 := SwapArithmetic(2, 2);
expect r0 == 2;
expect r1 == 2;
}

// REPEAT 3 - TIME: 3.2577327 s
