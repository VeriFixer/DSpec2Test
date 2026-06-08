
method {:test} Test36() {
var r0 := Min(114, 114);
expect r0 == 114 || r0 == 114;
expect r0 <= 114 && r0 <= 114;
}
method {:test} Test37() {
var r0 := Min(114, 113);
expect r0 == 114 || r0 == 113;
expect r0 <= 114 && r0 <= 113;
}

// REPEAT 10 - TIME: 19.0342682 s