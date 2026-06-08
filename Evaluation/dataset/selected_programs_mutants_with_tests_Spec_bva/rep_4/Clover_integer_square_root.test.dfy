
method {:test} Test8() {
var r0 := SquareRoot(10403);
expect r0 * r0 <= 10403 < (r0 + 1) * (r0 + 1);
}

// REPEAT 4 - TIME: 8.0251716 s