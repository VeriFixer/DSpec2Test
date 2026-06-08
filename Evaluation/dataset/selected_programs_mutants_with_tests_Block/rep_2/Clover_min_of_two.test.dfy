
method {:test} Test2() {
var r0 := Min(2, 2);
expect 2 <= 2 ==> r0 == 2;
expect 2 > 2 ==> r0 == 2;
}
method {:test} Test3() {
var r0 := Min(1, 2);
expect 1 <= 2 ==> r0 == 1;
expect 1 > 2 ==> r0 == 2;
}

// REPEAT 2 - TIME: 3.1995256 s