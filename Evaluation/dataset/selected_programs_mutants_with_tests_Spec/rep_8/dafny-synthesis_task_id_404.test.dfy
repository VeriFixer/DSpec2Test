
method {:test} Test14() {
var r0 := Min(11, 11);
expect r0 == 11 || r0 == 11;
expect r0 <= 11 && r0 <= 11;
}
method {:test} Test15() {
var r0 := Min(11, 10);
expect r0 == 11 || r0 == 10;
expect r0 <= 11 && r0 <= 10;
}

// REPEAT 8 - TIME: 11.7572159 s