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

method {:test} Test5() {
var r0, r1 := SwapBitvectors((160 as bv8), (160 as bv8));
expect r0 == (160 as bv8);
expect r1 == (160 as bv8);
}

// REPEAT 6 - TIME: 7.332552 s
