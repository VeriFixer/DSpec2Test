
method {:test} Test7() {
var r0 := SquareRoot(8);
expect r0 * r0 <= 8 < (r0 + 1) * (r0 + 1);
}

// REPEAT 8 - TIME: 15.1528766 s