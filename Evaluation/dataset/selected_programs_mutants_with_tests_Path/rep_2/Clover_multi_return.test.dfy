
method {:test} Test1() {
var r0, r1 := MultipleReturns(1, 1);
expect r0 == 1 + 1;
expect r1 == 1 - 1;
}

// REPEAT 2 - TIME: 3.9648963 s