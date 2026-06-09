
method {:test} Test11() {
var r0 := Swap(33, 32);
expect |r0| == 2;
expect r0[0] == 32;
expect r0[1] == 33;
}

// REPEAT 5 - TIME: 9.2036206 s