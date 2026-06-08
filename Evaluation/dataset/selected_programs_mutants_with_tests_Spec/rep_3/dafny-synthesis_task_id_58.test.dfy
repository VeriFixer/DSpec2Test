
method {:test} Test9() {
var r0 := HasOppositeSign(-3, 3);
expect r0 <==> (-3 < 0 && 3 > 0) || (-3 > 0 && 3 < 0);
}
method {:test} Test10() {
var r0 := HasOppositeSign(3, -3);
expect r0 <==> (3 < 0 && -3 > 0) || (3 > 0 && -3 < 0);
}
method {:test} Test11() {
var r0 := HasOppositeSign(3, 3);
expect r0 <==> (3 < 0 && 3 > 0) || (3 > 0 && 3 < 0);
}
method {:test} Test12() {
var r0 := HasOppositeSign(-3, -3);
expect r0 <==> (-3 < 0 && -3 > 0) || (-3 > 0 && -3 < 0);
}

// REPEAT 3 - TIME: 9.3317372 s