
method {:test} Test9() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 10 - TIME: 9.7931109 s