
method {:test} Test32() {
var r0 := Max(111, 111);
expect r0 == 111 || r0 == 111;
expect r0 >= 111 && r0 >= 111;
}
method {:test} Test33() {
var r0 := Max(110, 111);
expect r0 == 110 || r0 == 111;
expect r0 >= 110 && r0 >= 111;
}

// REPEAT 8 - TIME: 15.3643727 s