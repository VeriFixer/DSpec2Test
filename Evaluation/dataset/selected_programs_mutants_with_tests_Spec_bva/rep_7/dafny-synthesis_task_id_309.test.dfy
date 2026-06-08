
method {:test} Test30() {
var r0 := Max(109, 109);
expect r0 == 109 || r0 == 109;
expect r0 >= 109 && r0 >= 109;
}
method {:test} Test31() {
var r0 := Max(109, 110);
expect r0 == 109 || r0 == 110;
expect r0 >= 109 && r0 >= 110;
}

// REPEAT 7 - TIME: 16.2261708 s