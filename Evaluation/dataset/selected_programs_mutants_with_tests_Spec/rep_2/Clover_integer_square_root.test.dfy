
method {:test} Test1() {
var r0 := SquareRoot(3);
expect r0 * r0 <= 3 < (r0 + 1) * (r0 + 1);
}

// REPEAT 2 - TIME: 4.3558295 s