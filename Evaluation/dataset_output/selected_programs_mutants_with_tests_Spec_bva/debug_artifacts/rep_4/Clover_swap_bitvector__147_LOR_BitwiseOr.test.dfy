// Clover_swap_bitvector.dfy

method {:testEntry} SwapBitvectors(X: bv8, Y: bv8)
    returns (x: bv8, y: bv8)
  ensures x == Y
  ensures y == X
{
  x, y := X, Y;
  x := x ^ y;
  y := x | y;
  x := x ^ y;
}

method {:test} Test15() {
var r0, r1 := SwapBitvectors((192 as bv8), (192 as bv8));
expect r0 == (192 as bv8);
expect r1 == (192 as bv8);
}

// REPEAT 4 - TIME: 11.4792747 s
