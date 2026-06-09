
method {:test} Test12() {
var r0 := Min(10, 9);
expect 10 <= 9 ==> r0 == 10;
expect 10 > 9 ==> r0 == 9;
}
method {:test} Test13() {
var r0 := Min(9, 9);
expect 9 <= 9 ==> r0 == 9;
expect 9 > 9 ==> r0 == 9;
}

// REPEAT 7 - TIME: 11.8066822 s