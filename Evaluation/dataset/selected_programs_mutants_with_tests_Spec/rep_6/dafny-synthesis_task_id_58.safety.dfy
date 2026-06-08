method {:testEntry} HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
  result := (a < 0 && b > 0) || (a > 0 && b < 0);
}

method {:test} Test21() {
var r0 := HasOppositeSign(-6, 6);
expect r0 <==> (-6 < 0 && 6 > 0) || (-6 > 0 && 6 < 0);
}
method {:test} Test22() {
var r0 := HasOppositeSign(6, -6);
expect r0 <==> (6 < 0 && -6 > 0) || (6 > 0 && -6 < 0);
}
method {:test} Test23() {
var r0 := HasOppositeSign(6, 6);
expect r0 <==> (6 < 0 && 6 > 0) || (6 > 0 && 6 < 0);
}
method {:test} Test24() {
var r0 := HasOppositeSign(-6, -6);
expect r0 <==> (-6 < 0 && -6 > 0) || (-6 > 0 && -6 < 0);
}

// REPEAT 6 - TIME: 15.6224356 s
