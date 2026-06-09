
method {:test} Test10() {
var r0 := HasOppositeSign(4, 4);
expect r0 <==> (4 < 0 && 4 > 0) || (4 > 0 && 4 < 0);
}
method {:test} Test11() {
var r0 := HasOppositeSign(-4, 4);
expect r0 <==> (-4 < 0 && 4 > 0) || (-4 > 0 && 4 < 0);
}
method {:test} Test12() {
var r0 := HasOppositeSign(-4, -3);
expect r0 <==> (-4 < 0 && -3 > 0) || (-4 > 0 && -3 < 0);
}

// REPEAT 4 - TIME: 7.4850057 s