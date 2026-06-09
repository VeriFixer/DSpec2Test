
method {:test} Test8() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 5 - TIME: 7.6923161 s