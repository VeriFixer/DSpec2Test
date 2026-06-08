method {:testEntry} HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
  result := (a < 0 && b > 0) || (a > 0 && b < 0);
}

method {:test} Test29() {
var r0 := HasOppositeSign(-8, 8);
expect r0 <==> (-8 < 0 && 8 > 0) || (-8 > 0 && 8 < 0);
}
method {:test} Test30() {
var r0 := HasOppositeSign(8, -8);
expect r0 <==> (8 < 0 && -8 > 0) || (8 > 0 && -8 < 0);
}
method {:test} Test31() {
var r0 := HasOppositeSign(8, 8);
expect r0 <==> (8 < 0 && 8 > 0) || (8 > 0 && 8 < 0);
}
method {:test} Test32() {
var r0 := HasOppositeSign(-8, -8);
expect r0 <==> (-8 < 0 && -8 > 0) || (-8 > 0 && -8 < 0);
}

// REPEAT 8 - TIME: 19.6387179 s
