
method {:test} Test4() {
var r0 := Swap(32, 33);
expect |r0| == 2;
expect r0[0] == 33;
expect r0[1] == 32;
}

// REPEAT 5 - TIME: 4.9099634 s