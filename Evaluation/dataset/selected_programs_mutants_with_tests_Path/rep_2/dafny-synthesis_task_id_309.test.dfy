
method {:test} Test2() {
var r0 := Max(1, 1);
expect r0 == 1 || r0 == 1;
expect r0 >= 1 && r0 >= 1;
}
method {:test} Test3() {
var r0 := Max(1, 2);
expect r0 == 1 || r0 == 2;
expect r0 >= 1 && r0 >= 2;
}

// REPEAT 2 - TIME: 4.7936006 s