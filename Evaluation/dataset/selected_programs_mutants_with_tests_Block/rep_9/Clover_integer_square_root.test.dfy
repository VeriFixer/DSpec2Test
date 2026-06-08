
method {:test} Test8() {
var r0 := SquareRoot(9);
expect r0 * r0 <= 9 < (r0 + 1) * (r0 + 1);
}

// REPEAT 9 - TIME: 7.7216436 s