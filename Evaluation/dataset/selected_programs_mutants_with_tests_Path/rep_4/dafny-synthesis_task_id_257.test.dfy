
method {:test} Test3() {
var r0 := Swap(31, 30);
expect |r0| == 2;
expect r0[0] == 30;
expect r0[1] == 31;
}

// REPEAT 4 - TIME: 6.475218 s