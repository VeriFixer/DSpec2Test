
method {:test} Test18() {
var r0 := Min(14, 14);
expect 14 <= 14 ==> r0 == 14;
expect 14 > 14 ==> r0 == 14;
}
method {:test} Test19() {
var r0 := Min(13, 14);
expect 13 <= 14 ==> r0 == 13;
expect 13 > 14 ==> r0 == 14;
}

// REPEAT 10 - TIME: 10.8408914 s