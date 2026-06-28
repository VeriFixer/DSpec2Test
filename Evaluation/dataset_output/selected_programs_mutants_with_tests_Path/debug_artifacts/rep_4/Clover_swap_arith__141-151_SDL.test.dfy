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

method {:test} Test3() {
var r0, r1 := SwapArithmetic(3, 3);
expect r0 == 3;
expect r1 == 3;
}

// REPEAT 4 - TIME: 9.8480264 s
