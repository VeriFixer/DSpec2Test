
method {:test} Test37() {
var r0 := HasOppositeSign(-10, 10);
expect r0 <==> (-10 < 0 && 10 > 0) || (-10 > 0 && 10 < 0);
}
method {:test} Test38() {
var r0 := HasOppositeSign(10, -10);
expect r0 <==> (10 < 0 && -10 > 0) || (10 > 0 && -10 < 0);
}
method {:test} Test39() {
var r0 := HasOppositeSign(10, 10);
expect r0 <==> (10 < 0 && 10 > 0) || (10 > 0 && 10 < 0);
}
method {:test} Test40() {
var r0 := HasOppositeSign(-10, -10);
expect r0 <==> (-10 < 0 && -10 > 0) || (-10 > 0 && -10 < 0);
}

// REPEAT 10 - TIME: 21.5081543 s