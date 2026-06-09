
method {:test} Test7() {
var r0, r1 := MultipleReturns(7, 7);
expect r0 == 7 + 7;
expect r1 == 7 - 7;
}

// REPEAT 8 - TIME: 6.4780926 s