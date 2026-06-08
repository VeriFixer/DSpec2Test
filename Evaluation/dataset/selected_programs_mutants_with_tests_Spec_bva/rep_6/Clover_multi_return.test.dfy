
method {:test} Test17() {
var r0, r1 := MultipleReturns(105, 105);
expect r0 == 105 + 105;
expect r1 == 105 - 105;
}

// REPEAT 6 - TIME: 10.897304 s