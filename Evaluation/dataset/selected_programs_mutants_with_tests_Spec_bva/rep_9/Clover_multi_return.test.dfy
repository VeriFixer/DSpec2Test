
method {:test} Test20() {
var r0, r1 := MultipleReturns(108, 108);
expect r0 == 108 + 108;
expect r1 == 108 - 108;
}

// REPEAT 9 - TIME: 12.4724411 s