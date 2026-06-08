
method {:test} Test9() {
var r0 := SquareRoot(10608);
expect r0 * r0 <= 10608 < (r0 + 1) * (r0 + 1);
}

// REPEAT 5 - TIME: 8.7058392 s