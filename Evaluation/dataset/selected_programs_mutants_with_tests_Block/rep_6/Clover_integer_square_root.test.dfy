
method {:test} Test5() {
var r0 := SquareRoot(6);
expect r0 * r0 <= 6 < (r0 + 1) * (r0 + 1);
}

// REPEAT 6 - TIME: 5.2803689 s