
method {:test} Test10() {
var r0 := Max(7, 7);
expect r0 == 7 || r0 == 7;
expect r0 >= 7 && r0 >= 7;
}
method {:test} Test11() {
var r0 := Max(7, 8);
expect r0 == 7 || r0 == 8;
expect r0 >= 7 && r0 >= 8;
}

// REPEAT 6 - TIME: 11.0543354 s