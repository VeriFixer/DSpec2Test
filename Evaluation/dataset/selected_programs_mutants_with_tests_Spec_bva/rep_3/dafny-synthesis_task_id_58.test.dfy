
method {:test} Test45() {
var r0 := HasOppositeSign(-3, 102);
expect r0 <==> (-3 < 0 && 102 > 0) || (-3 > 0 && 102 < 0);
}
method {:test} Test46() {
var r0 := HasOppositeSign(102, -3);
expect r0 <==> (102 < 0 && -3 > 0) || (102 > 0 && -3 < 0);
}
method {:test} Test47() {
var r0 := HasOppositeSign(102, 102);
expect r0 <==> (102 < 0 && 102 > 0) || (102 > 0 && 102 < 0);
}
method {:test} Test48() {
var r0 := HasOppositeSign(-3, -3);
expect r0 <==> (-3 < 0 && -3 > 0) || (-3 > 0 && -3 < 0);
}

// REPEAT 3 - TIME: 22.7799732 s