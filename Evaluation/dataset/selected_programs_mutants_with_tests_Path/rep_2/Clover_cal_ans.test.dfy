
method {:test} Test1() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 2 - TIME: 8.7318777 s