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

method {:test} Test16() {
var r0, r1 := SwapBitvectors((32 as bv8), (32 as bv8));
expect r0 == (32 as bv8);
expect r1 == (32 as bv8);
}

// REPEAT 5 - TIME: 12.3353756 s
