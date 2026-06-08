
method {:test} Test16() {
var r0, r1 := MultipleReturns(104, 104);
expect r0 == 104 + 104;
expect r1 == 104 - 104;
}

// REPEAT 5 - TIME: 10.0975618 s