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

method {:test} Test8() {
var r0, r1 := SwapArithmetic(8, 8);
expect r0 == 8;
expect r1 == 8;
}

// REPEAT 9 - TIME: 11.9904162 s
