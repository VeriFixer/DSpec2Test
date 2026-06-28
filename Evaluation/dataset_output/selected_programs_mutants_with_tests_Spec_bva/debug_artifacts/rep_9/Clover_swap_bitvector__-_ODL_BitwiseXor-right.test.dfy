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

method {:test} Test20() {
var r0, r1 := SwapBitvectors((16 as bv8), (16 as bv8));
expect r0 == (16 as bv8);
expect r1 == (16 as bv8);
}

// REPEAT 9 - TIME: 19.7822025 s
