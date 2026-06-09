
method {:test} Test5() {
var r0 := SquareRoot(16);
expect r0 * r0 <= 16 < (r0 + 1) * (r0 + 1);
}

// REPEAT 6 - TIME: 6.2634601 s