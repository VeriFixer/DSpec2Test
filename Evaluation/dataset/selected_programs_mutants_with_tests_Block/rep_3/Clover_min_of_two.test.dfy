
method {:test} Test4() {
var r0 := Min(3, 3);
expect 3 <= 3 ==> r0 == 3;
expect 3 > 3 ==> r0 == 3;
}
method {:test} Test5() {
var r0 := Min(3, 4);
expect 3 <= 4 ==> r0 == 3;
expect 3 > 4 ==> r0 == 4;
}

// REPEAT 3 - TIME: 4.1513518 s