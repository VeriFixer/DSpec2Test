
method {:test} Test36() {
var r0 := Min(114, 113);
expect 114 <= 113 ==> r0 == 114;
expect 114 > 113 ==> r0 == 113;
}
method {:test} Test37() {
var r0 := Min(114, 114);
expect 114 <= 114 ==> r0 == 114;
expect 114 > 114 ==> r0 == 114;
}

// REPEAT 10 - TIME: 29.1315167 s