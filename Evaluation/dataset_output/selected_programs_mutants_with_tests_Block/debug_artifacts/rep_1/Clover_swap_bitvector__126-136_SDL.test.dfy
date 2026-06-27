// Clover_swap_bitvector.dfy

method {:testEntry} SwapBitvectors(X: bv8, Y: bv8)
    returns (x: bv8, y: bv8)
  ensures x == Y
  ensures y == X
{
  x, y := X, Y;
  y := x ^ y;
  x := x ^ y;
}

method {:test} Test0() {
var r0, r1 := SwapBitvectors((255 as bv8), (0 as bv8));
expect r0 == (0 as bv8);
expect r1 == (255 as bv8);
}

// REPEAT 1 - TIME: 3.1233572 s
