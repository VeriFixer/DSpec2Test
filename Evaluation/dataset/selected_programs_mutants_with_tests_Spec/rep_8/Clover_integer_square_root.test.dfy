
method {:test} Test7() {
var r0 := SquareRoot(25);
expect r0 * r0 <= 25 < (r0 + 1) * (r0 + 1);
}

// REPEAT 8 - TIME: 7.5706492 s