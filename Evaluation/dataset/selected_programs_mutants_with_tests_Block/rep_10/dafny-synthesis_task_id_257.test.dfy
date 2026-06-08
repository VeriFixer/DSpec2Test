
method {:test} Test9() {
var r0 := Swap(42, 43);
expect |r0| == 2;
expect r0[0] == 43;
expect r0[1] == 42;
}

// REPEAT 10 - TIME: 8.1953012 s