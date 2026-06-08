
method {:test} Test14() {
var r0 := SquareRoot(10819);
expect r0 * r0 <= 10819 < (r0 + 1) * (r0 + 1);
}

// REPEAT 10 - TIME: 11.9898092 s