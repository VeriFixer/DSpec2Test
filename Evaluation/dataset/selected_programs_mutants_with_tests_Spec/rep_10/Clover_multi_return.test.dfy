
method {:test} Test9() {
var r0, r1 := MultipleReturns(9, 9);
expect r0 == 9 + 9;
expect r1 == 9 - 9;
}

// REPEAT 10 - TIME: 10.5670712 s