
method {:test} Test4() {
var r0 := Min(3, 3);
expect r0 == 3 || r0 == 3;
expect r0 <= 3 && r0 <= 3;
}
method {:test} Test5() {
var r0 := Min(4, 3);
expect r0 == 4 || r0 == 3;
expect r0 <= 4 && r0 <= 3;
}

// REPEAT 3 - TIME: 5.25456 s