
method {:test} Test10() {
var r0 := Min(8, 7);
expect r0 == 8 || r0 == 7;
expect r0 <= 8 && r0 <= 7;
}
method {:test} Test11() {
var r0 := Min(8, 8);
expect r0 == 8 || r0 == 8;
expect r0 <= 8 && r0 <= 8;
}

// REPEAT 6 - TIME: 7.6727442 s