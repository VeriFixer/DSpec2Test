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

method {:test} Test9() {
var r0, r1 := SwapArithmetic(9, 9);
expect r0 == 9;
expect r1 == 9;
}

// REPEAT 10 - TIME: 17.801016 s
