
method {:test} Test28() {
var r0 := Min(108, 107);
expect 108 <= 107 ==> r0 == 108;
expect 108 > 107 ==> r0 == 107;
}
method {:test} Test29() {
var r0 := Min(108, 108);
expect 108 <= 108 ==> r0 == 108;
expect 108 > 108 ==> r0 == 108;
}

// REPEAT 6 - TIME: 23.4956542 s