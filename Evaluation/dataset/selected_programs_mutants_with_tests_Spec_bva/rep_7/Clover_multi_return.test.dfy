
method {:test} Test18() {
var r0, r1 := MultipleReturns(106, 106);
expect r0 == 106 + 106;
expect r1 == 106 - 106;
}

// REPEAT 7 - TIME: 11.6683955 s