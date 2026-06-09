
method {:test} Test6() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 7 - TIME: 5.7031266 s