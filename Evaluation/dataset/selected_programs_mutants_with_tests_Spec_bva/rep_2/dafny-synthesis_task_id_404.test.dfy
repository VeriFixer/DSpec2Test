
method {:test} Test20() {
var r0 := Min(102, 102);
expect r0 == 102 || r0 == 102;
expect r0 <= 102 && r0 <= 102;
}
method {:test} Test21() {
var r0 := Min(102, 101);
expect r0 == 102 || r0 == 101;
expect r0 <= 102 && r0 <= 101;
}

// REPEAT 2 - TIME: 11.7700506 s