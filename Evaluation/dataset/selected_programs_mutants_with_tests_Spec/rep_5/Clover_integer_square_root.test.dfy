
method {:test} Test4() {
var r0 := SquareRoot(15);
expect r0 * r0 <= 15 < (r0 + 1) * (r0 + 1);
}

// REPEAT 5 - TIME: 5.3780662 s