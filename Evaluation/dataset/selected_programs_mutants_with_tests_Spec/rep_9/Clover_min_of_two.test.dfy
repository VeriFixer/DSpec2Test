
method {:test} Test16() {
var r0 := Min(13, 12);
expect 13 <= 12 ==> r0 == 13;
expect 13 > 12 ==> r0 == 12;
}
method {:test} Test17() {
var r0 := Min(12, 12);
expect 12 <= 12 ==> r0 == 12;
expect 12 > 12 ==> r0 == 12;
}

// REPEAT 9 - TIME: 17.6273145 s