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

method {:test} Test7() {
var r0, r1 := SwapBitvectors((224 as bv8), (224 as bv8));
expect r0 == (224 as bv8);
expect r1 == (224 as bv8);
}

// REPEAT 8 - TIME: 9.6566356 s
