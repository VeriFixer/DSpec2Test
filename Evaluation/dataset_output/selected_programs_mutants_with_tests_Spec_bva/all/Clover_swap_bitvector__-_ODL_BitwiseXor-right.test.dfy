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


method {:test} Test0() {
var r0, r1 := SwapBitvectors((0 as bv8), (0 as bv8));
expect r0 == (0 as bv8);
expect r1 == (0 as bv8);
}

// REPEAT 1 - TIME: 9.2359879 s

method {:test} Test13() {
var r0, r1 := SwapBitvectors((128 as bv8), (128 as bv8));
expect r0 == (128 as bv8);
expect r1 == (128 as bv8);
}

// REPEAT 2 - TIME: 9.9422029 s

method {:test} Test14() {
var r0, r1 := SwapBitvectors((64 as bv8), (64 as bv8));
expect r0 == (64 as bv8);
expect r1 == (64 as bv8);
}

// REPEAT 3 - TIME: 10.7586312 s

method {:test} Test15() {
var r0, r1 := SwapBitvectors((192 as bv8), (192 as bv8));
expect r0 == (192 as bv8);
expect r1 == (192 as bv8);
}

// REPEAT 4 - TIME: 11.4792747 s

method {:test} Test16() {
var r0, r1 := SwapBitvectors((32 as bv8), (32 as bv8));
expect r0 == (32 as bv8);
expect r1 == (32 as bv8);
}

// REPEAT 5 - TIME: 12.3353756 s

method {:test} Test17() {
var r0, r1 := SwapBitvectors((160 as bv8), (160 as bv8));
expect r0 == (160 as bv8);
expect r1 == (160 as bv8);
}

// REPEAT 6 - TIME: 13.2416198 s

method {:test} Test18() {
var r0, r1 := SwapBitvectors((96 as bv8), (96 as bv8));
expect r0 == (96 as bv8);
expect r1 == (96 as bv8);
}

// REPEAT 7 - TIME: 13.9726749 s

method {:test} Test19() {
var r0, r1 := SwapBitvectors((224 as bv8), (224 as bv8));
expect r0 == (224 as bv8);
expect r1 == (224 as bv8);
}

// REPEAT 8 - TIME: 14.6701395 s

method {:test} Test20() {
var r0, r1 := SwapBitvectors((16 as bv8), (16 as bv8));
expect r0 == (16 as bv8);
expect r1 == (16 as bv8);
}

// REPEAT 9 - TIME: 15.5051897 s

method {:test} Test21() {
var r0, r1 := SwapBitvectors((144 as bv8), (144 as bv8));
expect r0 == (144 as bv8);
expect r1 == (144 as bv8);
}

// REPEAT 10 - TIME: 16.1738235 s
