
method {:test} Test8() {
var r0 := Min(6, 6);
expect r0 == 6 || r0 == 6;
expect r0 <= 6 && r0 <= 6;
}
method {:test} Test9() {
var r0 := Min(7, 6);
expect r0 == 7 || r0 == 6;
expect r0 <= 7 && r0 <= 6;
}

// REPEAT 5 - TIME: 10.1039893 s