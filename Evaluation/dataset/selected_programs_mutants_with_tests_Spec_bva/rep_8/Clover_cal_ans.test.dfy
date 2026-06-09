
method {:test} Test11() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 8 - TIME: 9.7261015 s