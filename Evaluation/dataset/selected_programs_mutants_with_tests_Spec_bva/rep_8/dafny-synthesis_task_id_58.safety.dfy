method {:testEntry} HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
  result := (a < 0 && b > 0) || (a > 0 && b < 0);
}

method {:test} Test65() {
var r0 := HasOppositeSign(-8, 107);
expect r0 <==> (-8 < 0 && 107 > 0) || (-8 > 0 && 107 < 0);
}
method {:test} Test66() {
var r0 := HasOppositeSign(107, -8);
expect r0 <==> (107 < 0 && -8 > 0) || (107 > 0 && -8 < 0);
}
method {:test} Test67() {
var r0 := HasOppositeSign(107, 107);
expect r0 <==> (107 < 0 && 107 > 0) || (107 > 0 && 107 < 0);
}
method {:test} Test68() {
var r0 := HasOppositeSign(-8, -8);
expect r0 <==> (-8 < 0 && -8 > 0) || (-8 > 0 && -8 < 0);
}

// REPEAT 8 - TIME: 30.9197372 s
