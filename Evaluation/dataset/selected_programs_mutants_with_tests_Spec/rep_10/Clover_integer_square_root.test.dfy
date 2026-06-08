
method {:test} Test9() {
var r0 := SquareRoot(35);
expect r0 * r0 <= 35 < (r0 + 1) * (r0 + 1);
}

// REPEAT 10 - TIME: 10.0918789 s