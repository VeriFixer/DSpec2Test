
method {:test} Test28() {
var r0 := Max(108, 108);
expect r0 == 108 || r0 == 108;
expect r0 >= 108 && r0 >= 108;
}
method {:test} Test29() {
var r0 := Max(107, 108);
expect r0 == 107 || r0 == 108;
expect r0 >= 107 && r0 >= 108;
}

// REPEAT 6 - TIME: 15.279799 s