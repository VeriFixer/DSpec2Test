
method {:test} Test20() {
var r0 := Min(102, 101);
expect 102 <= 101 ==> r0 == 102;
expect 102 > 101 ==> r0 == 101;
}
method {:test} Test21() {
var r0 := Min(102, 102);
expect 102 <= 102 ==> r0 == 102;
expect 102 > 102 ==> r0 == 102;
}

// REPEAT 2 - TIME: 14.6902901 s