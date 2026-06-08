
method {:test} Test8() {
var r0 := Min(7, 6);
expect 7 <= 6 ==> r0 == 7;
expect 7 > 6 ==> r0 == 6;
}
method {:test} Test9() {
var r0 := Min(6, 6);
expect 6 <= 6 ==> r0 == 6;
expect 6 > 6 ==> r0 == 6;
}

// REPEAT 5 - TIME: 11.1553513 s