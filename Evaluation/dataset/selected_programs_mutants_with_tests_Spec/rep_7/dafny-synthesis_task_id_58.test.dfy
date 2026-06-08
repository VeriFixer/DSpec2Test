
method {:test} Test25() {
var r0 := HasOppositeSign(-7, 7);
expect r0 <==> (-7 < 0 && 7 > 0) || (-7 > 0 && 7 < 0);
}
method {:test} Test26() {
var r0 := HasOppositeSign(7, -7);
expect r0 <==> (7 < 0 && -7 > 0) || (7 > 0 && -7 < 0);
}
method {:test} Test27() {
var r0 := HasOppositeSign(7, 7);
expect r0 <==> (7 < 0 && 7 > 0) || (7 > 0 && 7 < 0);
}
method {:test} Test28() {
var r0 := HasOppositeSign(-7, -7);
expect r0 <==> (-7 < 0 && -7 > 0) || (-7 > 0 && -7 < 0);
}

// REPEAT 7 - TIME: 17.5904022 s