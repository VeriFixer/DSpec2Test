
method {:test} Test6() {
var r0 := SquareRoot(24);
expect r0 * r0 <= 24 < (r0 + 1) * (r0 + 1);
}

// REPEAT 7 - TIME: 8.4266013 s