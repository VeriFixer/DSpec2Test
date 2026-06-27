// Clover_swap_bitvector.dfy

method {:testEntry} SwapBitvectors(X: bv8, Y: bv8)
    returns (x: bv8, y: bv8)
  ensures x == Y
  ensures y == X
{
  x, y := X, Y;
  x := x & y;
  y := x ^ y;
  x := x ^ y;
}

method {:test} Test0() {
var r0, r1 := SwapBitvectors((0 as bv8), (0 as bv8));
expect r0 == (0 as bv8);
expect r1 == (0 as bv8);
}

// REPEAT 1 - TIME: 9.2359879 s
