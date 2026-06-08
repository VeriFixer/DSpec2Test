
method {:test} Test13() {
var r0 := HasOppositeSign(-4, 4);
expect r0 <==> (-4 < 0 && 4 > 0) || (-4 > 0 && 4 < 0);
}
method {:test} Test14() {
var r0 := HasOppositeSign(4, -4);
expect r0 <==> (4 < 0 && -4 > 0) || (4 > 0 && -4 < 0);
}
method {:test} Test15() {
var r0 := HasOppositeSign(4, 4);
expect r0 <==> (4 < 0 && 4 > 0) || (4 > 0 && 4 < 0);
}
method {:test} Test16() {
var r0 := HasOppositeSign(-4, -4);
expect r0 <==> (-4 < 0 && -4 > 0) || (-4 > 0 && -4 < 0);
}

// REPEAT 4 - TIME: 11.3150077 s