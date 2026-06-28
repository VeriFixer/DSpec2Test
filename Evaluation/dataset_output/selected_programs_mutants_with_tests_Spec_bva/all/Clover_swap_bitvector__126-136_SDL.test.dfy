// Clover_swap_bitvector.dfy

method {:testEntry} SwapBitvectors(X: bv8, Y: bv8)
    returns (x: bv8, y: bv8)
  ensures x == Y
  ensures y == X
{
  x, y := X, Y;
  y := x ^ y;
  x := x ^ y;
}


method {:test} Test0() {
var r0, r1 := SwapBitvectors((0 as bv8), (0 as bv8));
expect r0 == (0 as bv8);
expect r1 == (0 as bv8);
}

// REPEAT 1 - TIME: 11.0858725 s

method {:test} Test13() {
var r0, r1 := SwapBitvectors((128 as bv8), (128 as bv8));
expect r0 == (128 as bv8);
expect r1 == (128 as bv8);
}

// REPEAT 2 - TIME: 12.2911503 s

method {:test} Test14() {
var r0, r1 := SwapBitvectors((64 as bv8), (64 as bv8));
expect r0 == (64 as bv8);
expect r1 == (64 as bv8);
}

// REPEAT 3 - TIME: 13.599719 s

method {:test} Test15() {
var r0, r1 := SwapBitvectors((192 as bv8), (192 as bv8));
expect r0 == (192 as bv8);
expect r1 == (192 as bv8);
}

// REPEAT 4 - TIME: 14.7452576 s

method {:test} Test16() {
var r0, r1 := SwapBitvectors((32 as bv8), (32 as bv8));
expect r0 == (32 as bv8);
expect r1 == (32 as bv8);
}

// REPEAT 5 - TIME: 15.7436732 s

method {:test} Test17() {
var r0, r1 := SwapBitvectors((160 as bv8), (160 as bv8));
expect r0 == (160 as bv8);
expect r1 == (160 as bv8);
}

// REPEAT 6 - TIME: 16.9535808 s

method {:test} Test18() {
var r0, r1 := SwapBitvectors((96 as bv8), (96 as bv8));
expect r0 == (96 as bv8);
expect r1 == (96 as bv8);
}

// REPEAT 7 - TIME: 17.8825738 s

method {:test} Test19() {
var r0, r1 := SwapBitvectors((224 as bv8), (224 as bv8));
expect r0 == (224 as bv8);
expect r1 == (224 as bv8);
}

// REPEAT 8 - TIME: 18.8504467 s

method {:test} Test20() {
var r0, r1 := SwapBitvectors((16 as bv8), (16 as bv8));
expect r0 == (16 as bv8);
expect r1 == (16 as bv8);
}

// REPEAT 9 - TIME: 19.7822025 s

method {:test} Test21() {
var r0, r1 := SwapBitvectors((144 as bv8), (144 as bv8));
expect r0 == (144 as bv8);
expect r1 == (144 as bv8);
}

// REPEAT 10 - TIME: 20.7796372 s
