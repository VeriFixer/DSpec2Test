
method {:test} Test13() {
var r0, r1 := MultipleReturns(101, 101);
expect r0 == 101 + 101;
expect r1 == 101 - 101;
}

// REPEAT 2 - TIME: 7.629115 s