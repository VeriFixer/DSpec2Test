
method {:test} Test13() {
var r0 := HasOppositeSign(-5, -4);
expect r0 <==> (-5 < 0 && -4 > 0) || (-5 > 0 && -4 < 0);
}
method {:test} Test14() {
var r0 := HasOppositeSign(-5, 5);
expect r0 <==> (-5 < 0 && 5 > 0) || (-5 > 0 && 5 < 0);
}
method {:test} Test16() {
var r0 := HasOppositeSign(5, 5);
expect r0 <==> (5 < 0 && 5 > 0) || (5 > 0 && 5 < 0);
}

// REPEAT 5 - TIME: 10.160147 s