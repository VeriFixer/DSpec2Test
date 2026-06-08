
method {:test} Test14() {
var r0 := Max(10, 10);
expect r0 == 10 || r0 == 10;
expect r0 >= 10 && r0 >= 10;
}
method {:test} Test15() {
var r0 := Max(10, 11);
expect r0 == 10 || r0 == 11;
expect r0 >= 10 && r0 >= 11;
}

// REPEAT 8 - TIME: 13.3730822 s