
method {:test} Test16() {
var r0 := HasOppositeSign(-6, -5);
expect r0 <==> (-6 < 0 && -5 > 0) || (-6 > 0 && -5 < 0);
}
method {:test} Test17() {
var r0 := HasOppositeSign(-6, 6);
expect r0 <==> (-6 < 0 && 6 > 0) || (-6 > 0 && 6 < 0);
}
method {:test} Test18() {
var r0 := HasOppositeSign(6, 6);
expect r0 <==> (6 < 0 && 6 > 0) || (6 > 0 && 6 < 0);
}

// REPEAT 6 - TIME: 22.2019383 s