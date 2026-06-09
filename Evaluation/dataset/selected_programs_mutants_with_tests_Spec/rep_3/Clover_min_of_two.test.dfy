
method {:test} Test4() {
var r0 := Min(4, 3);
expect 4 <= 3 ==> r0 == 4;
expect 4 > 3 ==> r0 == 3;
}
method {:test} Test5() {
var r0 := Min(3, 3);
expect 3 <= 3 ==> r0 == 3;
expect 3 > 3 ==> r0 == 3;
}

// REPEAT 3 - TIME: 6.5100513 s