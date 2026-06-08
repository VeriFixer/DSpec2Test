
method {:test} Test5() {
var r0, r1 := MultipleReturns(5, 5);
expect r0 == 5 + 5;
expect r1 == 5 - 5;
}

// REPEAT 6 - TIME: 8.1795146 s