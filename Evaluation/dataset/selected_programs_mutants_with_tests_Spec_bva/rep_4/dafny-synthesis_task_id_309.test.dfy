
method {:test} Test24() {
var r0 := Max(105, 105);
expect r0 == 105 || r0 == 105;
expect r0 >= 105 && r0 >= 105;
}
method {:test} Test25() {
var r0 := Max(104, 105);
expect r0 == 104 || r0 == 105;
expect r0 >= 104 && r0 >= 105;
}

// REPEAT 4 - TIME: 13.3497738 s