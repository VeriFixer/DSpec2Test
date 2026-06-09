
method {:test} Test19() {
var r0, r1 := MultipleReturns(107, 107);
expect r0 == 107 + 107;
expect r1 == 107 - 107;
}

// REPEAT 8 - TIME: 11.8710767 s