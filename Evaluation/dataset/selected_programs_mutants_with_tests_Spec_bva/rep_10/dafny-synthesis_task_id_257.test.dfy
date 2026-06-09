
method {:test} Test16() {
var r0 := Swap(43, 42);
expect |r0| == 2;
expect r0[0] == 42;
expect r0[1] == 43;
}

// REPEAT 10 - TIME: 12.691533 s