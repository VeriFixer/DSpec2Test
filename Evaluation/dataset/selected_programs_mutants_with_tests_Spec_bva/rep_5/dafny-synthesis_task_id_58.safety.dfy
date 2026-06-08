method {:testEntry} HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
  result := (a < 0 && b > 0) || (a > 0 && b < 0);
}

method {:test} Test53() {
var r0 := HasOppositeSign(-5, 104);
expect r0 <==> (-5 < 0 && 104 > 0) || (-5 > 0 && 104 < 0);
}
method {:test} Test54() {
var r0 := HasOppositeSign(104, -5);
expect r0 <==> (104 < 0 && -5 > 0) || (104 > 0 && -5 < 0);
}
method {:test} Test55() {
var r0 := HasOppositeSign(104, 104);
expect r0 <==> (104 < 0 && 104 > 0) || (104 > 0 && 104 < 0);
}
method {:test} Test56() {
var r0 := HasOppositeSign(-5, -5);
expect r0 <==> (-5 < 0 && -5 > 0) || (-5 > 0 && -5 < 0);
}

// REPEAT 5 - TIME: 28.6384663 s
