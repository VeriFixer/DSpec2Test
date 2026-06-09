
method {:test} Test36() {
var r0 := Max(114, 114);
expect r0 == 114 || r0 == 114;
expect r0 >= 114 && r0 >= 114;
}
method {:test} Test37() {
var r0 := Max(113, 114);
expect r0 == 113 || r0 == 114;
expect r0 >= 113 && r0 >= 114;
}

// REPEAT 10 - TIME: 17.0351091 s