
method {:test} Test61() {
var r0 := HasOppositeSign(-7, 106);
expect r0 <==> (-7 < 0 && 106 > 0) || (-7 > 0 && 106 < 0);
}
method {:test} Test62() {
var r0 := HasOppositeSign(106, -7);
expect r0 <==> (106 < 0 && -7 > 0) || (106 > 0 && -7 < 0);
}
method {:test} Test63() {
var r0 := HasOppositeSign(106, 106);
expect r0 <==> (106 < 0 && 106 > 0) || (106 > 0 && 106 < 0);
}
method {:test} Test64() {
var r0 := HasOppositeSign(-7, -7);
expect r0 <==> (-7 < 0 && -7 > 0) || (-7 > 0 && -7 < 0);
}

// REPEAT 7 - TIME: 32.5756037 s