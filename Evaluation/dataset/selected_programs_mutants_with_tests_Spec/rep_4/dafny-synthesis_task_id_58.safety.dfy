method {:testEntry} HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
  result := (a < 0 && b > 0) || (a > 0 && b < 0);
}

method {:test} Test13() {
var r0 := HasOppositeSign(-4, 4);
expect r0 <==> (-4 < 0 && 4 > 0) || (-4 > 0 && 4 < 0);
}
method {:test} Test14() {
var r0 := HasOppositeSign(4, -4);
expect r0 <==> (4 < 0 && -4 > 0) || (4 > 0 && -4 < 0);
}
method {:test} Test15() {
var r0 := HasOppositeSign(4, 4);
expect r0 <==> (4 < 0 && 4 > 0) || (4 > 0 && 4 < 0);
}
method {:test} Test16() {
var r0 := HasOppositeSign(-4, -4);
expect r0 <==> (-4 < 0 && -4 > 0) || (-4 > 0 && -4 < 0);
}

// REPEAT 4 - TIME: 10.3863235 s
