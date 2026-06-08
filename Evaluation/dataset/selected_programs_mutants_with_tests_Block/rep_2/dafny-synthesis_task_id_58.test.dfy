
method {:test} Test3() {
var r0 := HasOppositeSign(-2, 2);
expect r0 <==> (-2 < 0 && 2 > 0) || (-2 > 0 && 2 < 0);
}
method {:test} Test5() {
var r0 := HasOppositeSign(-2, -1);
expect r0 <==> (-2 < 0 && -1 > 0) || (-2 > 0 && -1 < 0);
}
method {:test} Test6() {
var r0 := HasOppositeSign(2, 2);
expect r0 <==> (2 < 0 && 2 > 0) || (2 > 0 && 2 < 0);
}

// REPEAT 2 - TIME: 4.8414874 s