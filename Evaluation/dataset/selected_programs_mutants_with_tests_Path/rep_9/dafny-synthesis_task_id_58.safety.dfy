method {:testEntry} HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
  result := (a < 0 && b > 0) || (a > 0 && b < 0);
}

method {:test} Test25() {
var r0 := HasOppositeSign(-9, -8);
expect r0 <==> (-9 < 0 && -8 > 0) || (-9 > 0 && -8 < 0);
}
method {:test} Test26() {
var r0 := HasOppositeSign(-9, 9);
expect r0 <==> (-9 < 0 && 9 > 0) || (-9 > 0 && 9 < 0);
}
method {:test} Test27() {
var r0 := HasOppositeSign(9, 9);
expect r0 <==> (9 < 0 && 9 > 0) || (9 > 0 && 9 < 0);
}

// REPEAT 9 - TIME: 32.3388743 s
