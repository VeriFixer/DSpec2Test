
method {:test} Test9() {
var r0 := Swap(29, 28);
expect |r0| == 2;
expect r0[0] == 28;
expect r0[1] == 29;
}

// REPEAT 3 - TIME: 7.7548671 s