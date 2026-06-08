
method {:test} Test32() {
var r0 := HasOppositeSign(10, 10);
expect r0 <==> (10 < 0 && 10 > 0) || (10 > 0 && 10 < 0);
}
method {:test} Test33() {
var r0 := HasOppositeSign(-10, 10);
expect r0 <==> (-10 < 0 && 10 > 0) || (-10 > 0 && 10 < 0);
}
method {:test} Test34() {
var r0 := HasOppositeSign(-10, -9);
expect r0 <==> (-10 < 0 && -9 > 0) || (-10 > 0 && -9 < 0);
}

// REPEAT 10 - TIME: 17.6420921 s