
method {:test} Test25() {
var r0 := HasOppositeSign(8, 8);
expect r0 <==> (8 < 0 && 8 > 0) || (8 > 0 && 8 < 0);
}
method {:test} Test26() {
var r0 := HasOppositeSign(-8, 8);
expect r0 <==> (-8 < 0 && 8 > 0) || (-8 > 0 && 8 < 0);
}
method {:test} Test27() {
var r0 := HasOppositeSign(-8, -7);
expect r0 <==> (-8 < 0 && -7 > 0) || (-8 > 0 && -7 < 0);
}

// REPEAT 8 - TIME: 13.286675 s