
method {:test} Test22() {
var r0 := HasOppositeSign(-8, -7);
expect r0 <==> (-8 < 0 && -7 > 0) || (-8 > 0 && -7 < 0);
}
method {:test} Test23() {
var r0 := HasOppositeSign(-8, 8);
expect r0 <==> (-8 < 0 && 8 > 0) || (-8 > 0 && 8 < 0);
}
method {:test} Test24() {
var r0 := HasOppositeSign(8, 8);
expect r0 <==> (8 < 0 && 8 > 0) || (8 > 0 && 8 < 0);
}

// REPEAT 8 - TIME: 28.6334076 s