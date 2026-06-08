
method {:test} Test73() {
var r0 := HasOppositeSign(-10, 109);
expect r0 <==> (-10 < 0 && 109 > 0) || (-10 > 0 && 109 < 0);
}
method {:test} Test74() {
var r0 := HasOppositeSign(109, -10);
expect r0 <==> (109 < 0 && -10 > 0) || (109 > 0 && -10 < 0);
}
method {:test} Test75() {
var r0 := HasOppositeSign(109, 109);
expect r0 <==> (109 < 0 && 109 > 0) || (109 > 0 && 109 < 0);
}
method {:test} Test76() {
var r0 := HasOppositeSign(-10, -10);
expect r0 <==> (-10 < 0 && -10 > 0) || (-10 > 0 && -10 < 0);
}

// REPEAT 10 - TIME: 38.0129972 s