
method {:test} Test1() {
var r0 := Swap(27, 26);
expect |r0| == 2;
expect r0[0] == 26;
expect r0[1] == 27;
}

// REPEAT 2 - TIME: 3.4203805 s