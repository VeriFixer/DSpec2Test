method {:testEntry} HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
  result := (a < 0 && b > 0) || (a > 0 && b < 0);
}

method {:test} Test5() {
var r0 := HasOppositeSign(-2, 2);
expect r0 <==> (-2 < 0 && 2 > 0) || (-2 > 0 && 2 < 0);
}
method {:test} Test6() {
var r0 := HasOppositeSign(2, -2);
expect r0 <==> (2 < 0 && -2 > 0) || (2 > 0 && -2 < 0);
}
method {:test} Test7() {
var r0 := HasOppositeSign(2, 2);
expect r0 <==> (2 < 0 && 2 > 0) || (2 > 0 && 2 < 0);
}
method {:test} Test8() {
var r0 := HasOppositeSign(-2, -2);
expect r0 <==> (-2 < 0 && -2 > 0) || (-2 > 0 && -2 < 0);
}

// REPEAT 2 - TIME: 6.4025494 s
