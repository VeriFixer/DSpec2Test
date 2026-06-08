method {:testEntry} HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
  result := (a < 0 && b > 0) || (a > 0 && b < 0);
}

method {:test} Test45() {
var r0 := HasOppositeSign(-3, 102);
expect r0 <==> (-3 < 0 && 102 > 0) || (-3 > 0 && 102 < 0);
}
method {:test} Test46() {
var r0 := HasOppositeSign(102, -3);
expect r0 <==> (102 < 0 && -3 > 0) || (102 > 0 && -3 < 0);
}
method {:test} Test47() {
var r0 := HasOppositeSign(102, 102);
expect r0 <==> (102 < 0 && 102 > 0) || (102 > 0 && 102 < 0);
}
method {:test} Test48() {
var r0 := HasOppositeSign(-3, -3);
expect r0 <==> (-3 < 0 && -3 > 0) || (-3 > 0 && -3 < 0);
}

// REPEAT 3 - TIME: 24.8010537 s
