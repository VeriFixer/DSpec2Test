
method {:test} Test2() {
var r0 := Min(2, 1);
expect 2 <= 1 ==> r0 == 2;
expect 2 > 1 ==> r0 == 1;
}
method {:test} Test3() {
var r0 := Min(2, 2);
expect 2 <= 2 ==> r0 == 2;
expect 2 > 2 ==> r0 == 2;
}

// REPEAT 2 - TIME: 5.6267728 s