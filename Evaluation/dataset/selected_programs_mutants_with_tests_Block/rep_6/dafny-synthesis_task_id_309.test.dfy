
method {:test} Test10() {
var r0 := Max(7, 8);
expect r0 == 7 || r0 == 8;
expect r0 >= 7 && r0 >= 8;
}
method {:test} Test11() {
var r0 := Max(7, 7);
expect r0 == 7 || r0 == 7;
expect r0 >= 7 && r0 >= 7;
}

// REPEAT 6 - TIME: 9.0234197 s