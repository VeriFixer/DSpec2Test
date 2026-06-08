
method {:test} Test11() {
var r0 := SquareRoot(10816);
expect r0 * r0 <= 10816 < (r0 + 1) * (r0 + 1);
}

// REPEAT 7 - TIME: 10.0322088 s