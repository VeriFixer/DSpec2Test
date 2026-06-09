
method {:test} Test14() {
var r0 := Min(11, 10);
expect 11 <= 10 ==> r0 == 11;
expect 11 > 10 ==> r0 == 10;
}
method {:test} Test15() {
var r0 := Min(11, 11);
expect 11 <= 11 ==> r0 == 11;
expect 11 > 11 ==> r0 == 11;
}

// REPEAT 8 - TIME: 13.0533474 s