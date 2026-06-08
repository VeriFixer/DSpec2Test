
method {:test} Test2() {
var r0 := Min(2, 1);
expect r0 == 2 || r0 == 1;
expect r0 <= 2 && r0 <= 1;
}
method {:test} Test3() {
var r0 := Min(2, 2);
expect r0 == 2 || r0 == 2;
expect r0 <= 2 && r0 <= 2;
}

// REPEAT 2 - TIME: 3.6781681 s