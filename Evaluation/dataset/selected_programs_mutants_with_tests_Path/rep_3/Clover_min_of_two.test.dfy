
method {:test} Test4() {
var r0 := Min(3, 4);
expect 3 <= 4 ==> r0 == 3;
expect 3 > 4 ==> r0 == 4;
}
method {:test} Test5() {
var r0 := Min(3, 3);
expect 3 <= 3 ==> r0 == 3;
expect 3 > 3 ==> r0 == 3;
}

// REPEAT 3 - TIME: 7.1754946 s