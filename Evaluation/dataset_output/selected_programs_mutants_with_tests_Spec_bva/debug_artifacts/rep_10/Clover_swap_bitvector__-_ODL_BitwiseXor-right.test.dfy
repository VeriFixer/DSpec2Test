// Clover_swap_bitvector.dfy

method {:testEntry} SwapBitvectors(X: bv8, Y: bv8)
    returns (x: bv8, y: bv8)
  ensures x == Y
  ensures y == X
{
  x, y := X, Y;
  x := x;
  y := x;
  x := x;
}

method {:test} Test21() {
var r0, r1 := SwapBitvectors((144 as bv8), (144 as bv8));
expect r0 == (144 as bv8);
expect r1 == (144 as bv8);
}

// REPEAT 10 - TIME: 16.1738235 s
