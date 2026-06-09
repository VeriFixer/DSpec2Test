
method {:test} Test16() {
var r0 := Min(12, 12);
expect 12 <= 12 ==> r0 == 12;
expect 12 > 12 ==> r0 == 12;
}
method {:test} Test17() {
var r0 := Min(12, 13);
expect 12 <= 13 ==> r0 == 12;
expect 12 > 13 ==> r0 == 13;
}

// REPEAT 9 - TIME: 9.2705919 s