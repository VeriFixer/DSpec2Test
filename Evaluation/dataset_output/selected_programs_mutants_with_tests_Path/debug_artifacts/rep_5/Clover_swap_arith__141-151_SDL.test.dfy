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

method {:test} Test4() {
var r0, r1 := SwapArithmetic(4, 4);
expect r0 == 4;
expect r1 == 4;
}

// REPEAT 5 - TIME: 11.2044245 s
