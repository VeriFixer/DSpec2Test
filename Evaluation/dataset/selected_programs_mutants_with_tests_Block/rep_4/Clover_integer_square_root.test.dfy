
method {:test} Test3() {
var r0 := SquareRoot(4);
expect r0 * r0 <= 4 < (r0 + 1) * (r0 + 1);
}

// REPEAT 4 - TIME: 4.1335012 s