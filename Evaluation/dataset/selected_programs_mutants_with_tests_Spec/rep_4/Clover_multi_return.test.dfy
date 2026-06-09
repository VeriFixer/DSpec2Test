
method {:test} Test3() {
var r0, r1 := MultipleReturns(3, 3);
expect r0 == 3 + 3;
expect r1 == 3 - 3;
}

// REPEAT 4 - TIME: 4.805996 s