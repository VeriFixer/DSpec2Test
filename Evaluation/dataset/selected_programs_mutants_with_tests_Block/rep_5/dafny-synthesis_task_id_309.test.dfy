
method {:test} Test8() {
var r0 := Max(5, 6);
expect r0 == 5 || r0 == 6;
expect r0 >= 5 && r0 >= 6;
}
method {:test} Test9() {
var r0 := Max(6, 6);
expect r0 == 6 || r0 == 6;
expect r0 >= 6 && r0 >= 6;
}

// REPEAT 5 - TIME: 7.924256 s