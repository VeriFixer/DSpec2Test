// Clover_swap_bitvector.dfy

method {:testEntry} SwapBitvectors(X: bv8, Y: bv8)
    returns (x: bv8, y: bv8)
  ensures x == Y
  ensures y == X
{
  x, y := X, Y;
  x := x ^ y;
  x := x ^ y;
}


method {:test} Test0() {
var r0, r1 := SwapBitvectors((255 as bv8), (0 as bv8));
expect r0 == (0 as bv8);
expect r1 == (255 as bv8);
}

// REPEAT 1 - TIME: 3.714306 s

method {:test} Test1() {
var r0, r1 := SwapBitvectors((0 as bv8), (128 as bv8));
expect r0 == (128 as bv8);
expect r1 == (0 as bv8);
}

// REPEAT 2 - TIME: 5.7406787 s

method {:test} Test2() {
var r0, r1 := SwapBitvectors((128 as bv8), (64 as bv8));
expect r0 == (64 as bv8);
expect r1 == (128 as bv8);
}

// REPEAT 3 - TIME: 7.3392231 s

method {:test} Test3() {
var r0, r1 := SwapBitvectors((64 as bv8), (192 as bv8));
expect r0 == (192 as bv8);
expect r1 == (64 as bv8);
}

// REPEAT 4 - TIME: 9.0670285 s

method {:test} Test4() {
var r0, r1 := SwapBitvectors((192 as bv8), (32 as bv8));
expect r0 == (32 as bv8);
expect r1 == (192 as bv8);
}

// REPEAT 5 - TIME: 10.8010528 s

method {:test} Test5() {
var r0, r1 := SwapBitvectors((32 as bv8), (160 as bv8));
expect r0 == (160 as bv8);
expect r1 == (32 as bv8);
}

// REPEAT 6 - TIME: 12.0373484 s

method {:test} Test6() {
var r0, r1 := SwapBitvectors((160 as bv8), (96 as bv8));
expect r0 == (96 as bv8);
expect r1 == (160 as bv8);
}

// REPEAT 7 - TIME: 13.3676894 s

method {:test} Test7() {
var r0, r1 := SwapBitvectors((96 as bv8), (224 as bv8));
expect r0 == (224 as bv8);
expect r1 == (96 as bv8);
}

// REPEAT 8 - TIME: 14.7027394 s

method {:test} Test8() {
var r0, r1 := SwapBitvectors((224 as bv8), (16 as bv8));
expect r0 == (16 as bv8);
expect r1 == (224 as bv8);
}

// REPEAT 9 - TIME: 15.978542 s

method {:test} Test9() {
var r0, r1 := SwapBitvectors((16 as bv8), (144 as bv8));
expect r0 == (144 as bv8);
expect r1 == (16 as bv8);
}

// REPEAT 10 - TIME: 17.3978343 s
