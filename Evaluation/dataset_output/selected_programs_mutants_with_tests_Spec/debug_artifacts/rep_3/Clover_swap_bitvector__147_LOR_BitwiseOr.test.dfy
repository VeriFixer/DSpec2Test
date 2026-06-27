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

method {:test} Test2() {
var r0, r1 := SwapBitvectors((64 as bv8), (64 as bv8));
expect r0 == (64 as bv8);
expect r1 == (64 as bv8);
}

// REPEAT 3 - TIME: 5.1997531 s
