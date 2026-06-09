
method {:test} Test19() {
var r0 := HasOppositeSign(-7, -6);
expect r0 <==> (-7 < 0 && -6 > 0) || (-7 > 0 && -6 < 0);
}
method {:test} Test20() {
var r0 := HasOppositeSign(-7, 7);
expect r0 <==> (-7 < 0 && 7 > 0) || (-7 > 0 && 7 < 0);
}
method {:test} Test21() {
var r0 := HasOppositeSign(7, 7);
expect r0 <==> (7 < 0 && 7 > 0) || (7 > 0 && 7 < 0);
}

// REPEAT 7 - TIME: 25.4940175 s