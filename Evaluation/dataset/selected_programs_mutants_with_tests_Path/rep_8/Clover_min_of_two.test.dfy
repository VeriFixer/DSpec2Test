
method {:test} Test14() {
var r0 := Min(10, 11);
expect 10 <= 11 ==> r0 == 10;
expect 10 > 11 ==> r0 == 11;
}
method {:test} Test15() {
var r0 := Min(11, 11);
expect 11 <= 11 ==> r0 == 11;
expect 11 > 11 ==> r0 == 11;
}

// REPEAT 8 - TIME: 14.7310067 s