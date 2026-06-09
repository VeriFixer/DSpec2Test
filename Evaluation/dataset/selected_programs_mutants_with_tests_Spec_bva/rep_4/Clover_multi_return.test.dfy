
method {:test} Test15() {
var r0, r1 := MultipleReturns(103, 103);
expect r0 == 103 + 103;
expect r1 == 103 - 103;
}

// REPEAT 4 - TIME: 9.0865643 s