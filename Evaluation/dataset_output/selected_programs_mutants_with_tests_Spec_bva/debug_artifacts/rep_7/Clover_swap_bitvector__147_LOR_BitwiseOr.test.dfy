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

method {:test} Test18() {
var r0, r1 := SwapBitvectors((96 as bv8), (96 as bv8));
expect r0 == (96 as bv8);
expect r1 == (96 as bv8);
}

// REPEAT 7 - TIME: 17.8825738 s
