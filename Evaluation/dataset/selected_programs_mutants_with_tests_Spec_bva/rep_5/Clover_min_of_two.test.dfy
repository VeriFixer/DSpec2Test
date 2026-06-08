
method {:test} Test26() {
var r0 := Min(107, 106);
expect 107 <= 106 ==> r0 == 107;
expect 107 > 106 ==> r0 == 106;
}
method {:test} Test27() {
var r0 := Min(106, 106);
expect 106 <= 106 ==> r0 == 106;
expect 106 > 106 ==> r0 == 106;
}

// REPEAT 5 - TIME: 21.9314486 s