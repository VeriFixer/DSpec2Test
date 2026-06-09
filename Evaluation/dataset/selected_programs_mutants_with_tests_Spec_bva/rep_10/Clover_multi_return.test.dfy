
method {:test} Test21() {
var r0, r1 := MultipleReturns(109, 109);
expect r0 == 109 + 109;
expect r1 == 109 - 109;
}

// REPEAT 10 - TIME: 13.04094 s