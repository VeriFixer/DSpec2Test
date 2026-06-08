
method {:test} Test14() {
var r0, r1 := MultipleReturns(102, 102);
expect r0 == 102 + 102;
expect r1 == 102 - 102;
}

// REPEAT 3 - TIME: 8.7405611 s