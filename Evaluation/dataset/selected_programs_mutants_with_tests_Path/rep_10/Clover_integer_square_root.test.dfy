
method {:test} Test9() {
var r0 := SquareRoot(10);
expect r0 * r0 <= 10 < (r0 + 1) * (r0 + 1);
}

// REPEAT 10 - TIME: 27.4165267 s