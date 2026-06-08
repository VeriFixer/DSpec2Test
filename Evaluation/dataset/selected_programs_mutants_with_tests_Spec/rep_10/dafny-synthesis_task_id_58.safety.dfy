method {:testEntry} HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
  result := (a < 0 && b > 0) || (a > 0 && b < 0);
}

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

// REPEAT 10 - TIME: 23.5749592 s
