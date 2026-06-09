
method {:test} Test4() {
var r0 := SquareRoot(5);
expect r0 * r0 <= 5 < (r0 + 1) * (r0 + 1);
}

// REPEAT 5 - TIME: 4.6091894 s