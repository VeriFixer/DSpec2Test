method {:testEntry} HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
  result := (a < 0 && b > 0) || (a > 0 && b < 0);
}

method {:test} Test69() {
var r0 := HasOppositeSign(-9, 108);
expect r0 <==> (-9 < 0 && 108 > 0) || (-9 > 0 && 108 < 0);
}
method {:test} Test70() {
var r0 := HasOppositeSign(108, -9);
expect r0 <==> (108 < 0 && -9 > 0) || (108 > 0 && -9 < 0);
}
method {:test} Test71() {
var r0 := HasOppositeSign(108, 108);
expect r0 <==> (108 < 0 && 108 > 0) || (108 > 0 && 108 < 0);
}
method {:test} Test72() {
var r0 := HasOppositeSign(-9, -9);
expect r0 <==> (-9 < 0 && -9 > 0) || (-9 > 0 && -9 < 0);
}

// REPEAT 9 - TIME: 36.1648255 s
