// Clover_swap_bitvector.dfy

method {:testEntry} SwapBitvectors(X: bv8, Y: bv8)
    returns (x: bv8, y: bv8)
  ensures x == Y
  ensures y == X
{
  x := x ^ y;
  x, y := X, Y;
  y := x ^ y;
  x := x ^ y;
}

method {:test} Test1() {
var r0, r1 := SwapBitvectors((0 as bv8), (128 as bv8));
expect r0 == (128 as bv8);
expect r1 == (0 as bv8);
}

// REPEAT 2 - TIME: 4.1305654 s
