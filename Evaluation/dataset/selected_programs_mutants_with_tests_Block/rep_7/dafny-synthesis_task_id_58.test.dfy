
method {:test} Test20() {
var r0 := HasOppositeSign(-7, 7);
expect r0 <==> (-7 < 0 && 7 > 0) || (-7 > 0 && 7 < 0);
}
method {:test} Test22() {
var r0 := HasOppositeSign(-7, -6);
expect r0 <==> (-7 < 0 && -6 > 0) || (-7 > 0 && -6 < 0);
}
method {:test} Test24() {
var r0 := HasOppositeSign(7, 7);
expect r0 <==> (7 < 0 && 7 > 0) || (7 > 0 && 7 < 0);
}

// REPEAT 7 - TIME: 12.0223311 s