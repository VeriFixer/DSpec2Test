
method {:test} Test16() {
var r0 := Max(11, 12);
expect r0 == 11 || r0 == 12;
expect r0 >= 11 && r0 >= 12;
}
method {:test} Test17() {
var r0 := Max(12, 12);
expect r0 == 12 || r0 == 12;
expect r0 >= 12 && r0 >= 12;
}

// REPEAT 9 - TIME: 10.8543047 s