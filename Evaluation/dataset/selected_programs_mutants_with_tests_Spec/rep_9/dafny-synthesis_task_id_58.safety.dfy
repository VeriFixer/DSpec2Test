method {:testEntry} HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
  result := (a < 0 && b > 0) || (a > 0 && b < 0);
}

method {:test} Test33() {
var r0 := HasOppositeSign(-9, 9);
expect r0 <==> (-9 < 0 && 9 > 0) || (-9 > 0 && 9 < 0);
}
method {:test} Test34() {
var r0 := HasOppositeSign(9, -9);
expect r0 <==> (9 < 0 && -9 > 0) || (9 > 0 && -9 < 0);
}
method {:test} Test35() {
var r0 := HasOppositeSign(9, 9);
expect r0 <==> (9 < 0 && 9 > 0) || (9 > 0 && 9 < 0);
}
method {:test} Test36() {
var r0 := HasOppositeSign(-9, -9);
expect r0 <==> (-9 < 0 && -9 > 0) || (-9 > 0 && -9 < 0);
}

// REPEAT 9 - TIME: 19.9130626 s
