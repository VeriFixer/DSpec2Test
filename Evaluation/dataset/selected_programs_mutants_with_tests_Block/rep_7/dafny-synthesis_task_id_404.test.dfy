
method {:test} Test12() {
var r0 := Min(10, 9);
expect r0 == 10 || r0 == 9;
expect r0 <= 10 && r0 <= 9;
}
method {:test} Test13() {
var r0 := Min(9, 9);
expect r0 == 9 || r0 == 9;
expect r0 <= 9 && r0 <= 9;
}

// REPEAT 7 - TIME: 9.6346817 s