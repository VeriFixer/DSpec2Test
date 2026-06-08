
method {:test} Test14() {
var r0 := Swap(39, 38);
expect |r0| == 2;
expect r0[0] == 38;
expect r0[1] == 39;
}

// REPEAT 8 - TIME: 11.4883015 s