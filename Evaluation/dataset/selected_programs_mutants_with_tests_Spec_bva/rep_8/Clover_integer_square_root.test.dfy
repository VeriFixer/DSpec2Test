
method {:test} Test12() {
var r0 := SquareRoot(10817);
expect r0 * r0 <= 10817 < (r0 + 1) * (r0 + 1);
}

// REPEAT 8 - TIME: 10.6679492 s