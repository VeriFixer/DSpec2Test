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

method {:test} Test5() {
var r0, r1 := SwapArithmetic(5, 5);
expect r0 == 5;
expect r1 == 5;
}

// REPEAT 6 - TIME: 4.8250866 s
