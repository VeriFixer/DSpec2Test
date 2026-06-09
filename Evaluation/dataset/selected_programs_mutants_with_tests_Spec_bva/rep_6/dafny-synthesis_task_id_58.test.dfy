
method {:test} Test57() {
var r0 := HasOppositeSign(-6, 105);
expect r0 <==> (-6 < 0 && 105 > 0) || (-6 > 0 && 105 < 0);
}
method {:test} Test58() {
var r0 := HasOppositeSign(105, -6);
expect r0 <==> (105 < 0 && -6 > 0) || (105 > 0 && -6 < 0);
}
method {:test} Test59() {
var r0 := HasOppositeSign(105, 105);
expect r0 <==> (105 < 0 && 105 > 0) || (105 > 0 && 105 < 0);
}
method {:test} Test60() {
var r0 := HasOppositeSign(-6, -6);
expect r0 <==> (-6 < 0 && -6 > 0) || (-6 > 0 && -6 < 0);
}

// REPEAT 6 - TIME: 27.5653959 s