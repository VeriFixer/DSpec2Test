
method {:test} Test6() {
var r0 := Swap(37, 36);
expect |r0| == 2;
expect r0[0] == 36;
expect r0[1] == 37;
}

// REPEAT 7 - TIME: 8.1409407 s