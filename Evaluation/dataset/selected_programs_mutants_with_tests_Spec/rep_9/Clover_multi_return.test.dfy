
method {:test} Test8() {
var r0, r1 := MultipleReturns(8, 8);
expect r0 == 8 + 8;
expect r1 == 8 - 8;
}

// REPEAT 9 - TIME: 8.6379941 s