
method {:test} Test6() {
var r0 := SquareRoot(7);
expect r0 * r0 <= 7 < (r0 + 1) * (r0 + 1);
}

// REPEAT 7 - TIME: 6.4227629 s