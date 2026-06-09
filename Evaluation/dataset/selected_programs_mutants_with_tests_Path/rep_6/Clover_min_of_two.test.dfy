
method {:test} Test10() {
var r0 := Min(7, 8);
expect 7 <= 8 ==> r0 == 7;
expect 7 > 8 ==> r0 == 8;
}
method {:test} Test11() {
var r0 := Min(8, 8);
expect 8 <= 8 ==> r0 == 8;
expect 8 > 8 ==> r0 == 8;
}

// REPEAT 6 - TIME: 12.1896273 s