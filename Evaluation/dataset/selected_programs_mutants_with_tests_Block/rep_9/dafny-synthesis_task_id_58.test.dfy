
method {:test} Test28() {
var r0 := HasOppositeSign(-9, -8);
expect r0 <==> (-9 < 0 && -8 > 0) || (-9 > 0 && -8 < 0);
}
method {:test} Test29() {
var r0 := HasOppositeSign(-9, 9);
expect r0 <==> (-9 < 0 && 9 > 0) || (-9 > 0 && 9 < 0);
}
method {:test} Test31() {
var r0 := HasOppositeSign(9, 9);
expect r0 <==> (9 < 0 && 9 > 0) || (9 > 0 && 9 < 0);
}

// REPEAT 9 - TIME: 16.2890627 s