
method {:test} Test10() {
var r0 := SquareRoot(10815);
expect r0 * r0 <= 10815 < (r0 + 1) * (r0 + 1);
}

// REPEAT 6 - TIME: 9.3650608 s