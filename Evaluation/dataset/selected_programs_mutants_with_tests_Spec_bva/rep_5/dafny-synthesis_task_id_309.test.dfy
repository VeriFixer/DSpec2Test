
method {:test} Test26() {
var r0 := Max(106, 106);
expect r0 == 106 || r0 == 106;
expect r0 >= 106 && r0 >= 106;
}
method {:test} Test27() {
var r0 := Max(106, 107);
expect r0 == 106 || r0 == 107;
expect r0 >= 106 && r0 >= 107;
}

// REPEAT 5 - TIME: 13.0021213 s