
method {:test} Test2() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 3 - TIME: 12.0318967 s