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

method {:test} Test13() {
var r0, r1 := SwapBitvectors((128 as bv8), (128 as bv8));
expect r0 == (128 as bv8);
expect r1 == (128 as bv8);
}

// REPEAT 2 - TIME: 9.9422029 s
