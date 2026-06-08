
method {:test} Test26() {
var r0 := Min(106, 106);
expect r0 == 106 || r0 == 106;
expect r0 <= 106 && r0 <= 106;
}
method {:test} Test27() {
var r0 := Min(107, 106);
expect r0 == 107 || r0 == 106;
expect r0 <= 107 && r0 <= 106;
}

// REPEAT 5 - TIME: 14.6311301 s