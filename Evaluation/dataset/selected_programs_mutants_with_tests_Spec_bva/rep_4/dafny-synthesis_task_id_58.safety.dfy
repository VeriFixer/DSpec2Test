method {:testEntry} HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
  result := (a < 0 && b > 0) || (a > 0 && b < 0);
}

method {:test} Test49() {
var r0 := HasOppositeSign(-4, 103);
expect r0 <==> (-4 < 0 && 103 > 0) || (-4 > 0 && 103 < 0);
}
method {:test} Test50() {
var r0 := HasOppositeSign(103, -4);
expect r0 <==> (103 < 0 && -4 > 0) || (103 > 0 && -4 < 0);
}
method {:test} Test51() {
var r0 := HasOppositeSign(103, 103);
expect r0 <==> (103 < 0 && 103 > 0) || (103 > 0 && 103 < 0);
}
method {:test} Test52() {
var r0 := HasOppositeSign(-4, -4);
expect r0 <==> (-4 < 0 && -4 > 0) || (-4 > 0 && -4 < 0);
}

// REPEAT 4 - TIME: 26.6459789 s
