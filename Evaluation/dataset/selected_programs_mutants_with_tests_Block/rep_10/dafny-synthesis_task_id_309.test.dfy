
method {:test} Test18() {
var r0 := Max(13, 14);
expect r0 == 13 || r0 == 14;
expect r0 >= 13 && r0 >= 14;
}
method {:test} Test19() {
var r0 := Max(13, 13);
expect r0 == 13 || r0 == 13;
expect r0 >= 13 && r0 >= 13;
}

// REPEAT 10 - TIME: 11.8106643 s