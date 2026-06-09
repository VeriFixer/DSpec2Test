method {:testEntry} HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
  result := (a < 0 && b > 0) || (a > 0 && b < 0);
}

method {:test} Test17() {
var r0 := HasOppositeSign(-5, 5);
expect r0 <==> (-5 < 0 && 5 > 0) || (-5 > 0 && 5 < 0);
}
method {:test} Test18() {
var r0 := HasOppositeSign(5, -5);
expect r0 <==> (5 < 0 && -5 > 0) || (5 > 0 && -5 < 0);
}
method {:test} Test19() {
var r0 := HasOppositeSign(5, 5);
expect r0 <==> (5 < 0 && 5 > 0) || (5 > 0 && 5 < 0);
}
method {:test} Test20() {
var r0 := HasOppositeSign(-5, -5);
expect r0 <==> (-5 < 0 && -5 > 0) || (-5 > 0 && -5 < 0);
}

// REPEAT 5 - TIME: 12.4668076 s
