
method {:test} Test21() {
var r0 := HasOppositeSign(-6, 6);
expect r0 <==> (-6 < 0 && 6 > 0) || (-6 > 0 && 6 < 0);
}
method {:test} Test22() {
var r0 := HasOppositeSign(6, -6);
expect r0 <==> (6 < 0 && -6 > 0) || (6 > 0 && -6 < 0);
}
method {:test} Test23() {
var r0 := HasOppositeSign(6, 6);
expect r0 <==> (6 < 0 && 6 > 0) || (6 > 0 && 6 < 0);
}
method {:test} Test24() {
var r0 := HasOppositeSign(-6, -6);
expect r0 <==> (-6 < 0 && -6 > 0) || (-6 > 0 && -6 < 0);
}

// REPEAT 6 - TIME: 14.3717862 s