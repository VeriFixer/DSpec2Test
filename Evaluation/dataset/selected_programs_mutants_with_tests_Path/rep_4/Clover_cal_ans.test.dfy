
method {:test} Test3() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 4 - TIME: 15.0206732 s