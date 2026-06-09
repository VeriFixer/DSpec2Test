
method {:test} Test8() {
var r0 := Swap(27, 26);
expect |r0| == 2;
expect r0[0] == 26;
expect r0[1] == 27;
}

// REPEAT 2 - TIME: 7.0076949 s