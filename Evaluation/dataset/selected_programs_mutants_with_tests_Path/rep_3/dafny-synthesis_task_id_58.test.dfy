
method {:test} Test7() {
var r0 := HasOppositeSign(-3, -2);
expect r0 <==> (-3 < 0 && -2 > 0) || (-3 > 0 && -2 < 0);
}
method {:test} Test8() {
var r0 := HasOppositeSign(-3, 3);
expect r0 <==> (-3 < 0 && 3 > 0) || (-3 > 0 && 3 < 0);
}
method {:test} Test9() {
var r0 := HasOppositeSign(3, 3);
expect r0 <==> (3 < 0 && 3 > 0) || (3 > 0 && 3 < 0);
}

// REPEAT 3 - TIME: 12.726962 s