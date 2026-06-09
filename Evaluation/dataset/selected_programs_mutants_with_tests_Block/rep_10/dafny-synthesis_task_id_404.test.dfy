
method {:test} Test18() {
var r0 := Min(14, 13);
expect r0 == 14 || r0 == 13;
expect r0 <= 14 && r0 <= 13;
}
method {:test} Test19() {
var r0 := Min(14, 14);
expect r0 == 14 || r0 == 14;
expect r0 <= 14 && r0 <= 14;
}

// REPEAT 10 - TIME: 11.2723448 s