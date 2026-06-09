
method {:test} Test6() {
var r0 := Min(5, 4);
expect 5 <= 4 ==> r0 == 5;
expect 5 > 4 ==> r0 == 4;
}
method {:test} Test7() {
var r0 := Min(5, 5);
expect 5 <= 5 ==> r0 == 5;
expect 5 > 5 ==> r0 == 5;
}

// REPEAT 4 - TIME: 8.1533531 s