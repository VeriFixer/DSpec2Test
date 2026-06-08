method {:testEntry} HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
  result := (a < 0 && b > 0) || (a > 0 && b < 0);
}

method {:test} Test41() {
var r0 := HasOppositeSign(-2, 101);
expect r0 <==> (-2 < 0 && 101 > 0) || (-2 > 0 && 101 < 0);
}
method {:test} Test42() {
var r0 := HasOppositeSign(101, -2);
expect r0 <==> (101 < 0 && -2 > 0) || (101 > 0 && -2 < 0);
}
method {:test} Test43() {
var r0 := HasOppositeSign(101, 101);
expect r0 <==> (101 < 0 && 101 > 0) || (101 > 0 && 101 < 0);
}
method {:test} Test44() {
var r0 := HasOppositeSign(-2, -2);
expect r0 <==> (-2 < 0 && -2 > 0) || (-2 > 0 && -2 < 0);
}

// REPEAT 2 - TIME: 22.8553581 s
