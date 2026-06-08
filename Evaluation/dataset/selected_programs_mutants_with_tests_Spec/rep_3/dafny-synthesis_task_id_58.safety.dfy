method {:testEntry} HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
  result := (a < 0 && b > 0) || (a > 0 && b < 0);
}

method {:test} Test9() {
var r0 := HasOppositeSign(-3, 3);
expect r0 <==> (-3 < 0 && 3 > 0) || (-3 > 0 && 3 < 0);
}
method {:test} Test10() {
var r0 := HasOppositeSign(3, -3);
expect r0 <==> (3 < 0 && -3 > 0) || (3 > 0 && -3 < 0);
}
method {:test} Test11() {
var r0 := HasOppositeSign(3, 3);
expect r0 <==> (3 < 0 && 3 > 0) || (3 > 0 && 3 < 0);
}
method {:test} Test12() {
var r0 := HasOppositeSign(-3, -3);
expect r0 <==> (-3 < 0 && -3 > 0) || (-3 > 0 && -3 < 0);
}

// REPEAT 3 - TIME: 9.3317372 s
