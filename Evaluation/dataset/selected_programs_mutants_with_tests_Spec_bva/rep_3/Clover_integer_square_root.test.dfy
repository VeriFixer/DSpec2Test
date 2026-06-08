
method {:test} Test7() {
var r0 := SquareRoot(10200);
expect r0 * r0 <= 10200 < (r0 + 1) * (r0 + 1);
}

// REPEAT 3 - TIME: 7.3021155 s