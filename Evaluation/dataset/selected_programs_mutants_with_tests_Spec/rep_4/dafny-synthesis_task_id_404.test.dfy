
method {:test} Test6() {
var r0 := Min(5, 5);
expect r0 == 5 || r0 == 5;
expect r0 <= 5 && r0 <= 5;
}
method {:test} Test7() {
var r0 := Min(5, 4);
expect r0 == 5 || r0 == 4;
expect r0 <= 5 && r0 <= 4;
}

// REPEAT 4 - TIME: 6.8377773 s