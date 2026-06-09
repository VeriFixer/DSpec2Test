
method {:test} Test6() {
var r0 := SquareRoot(10001);
expect r0 * r0 <= 10001 < (r0 + 1) * (r0 + 1);
}

// REPEAT 2 - TIME: 6.1005344 s