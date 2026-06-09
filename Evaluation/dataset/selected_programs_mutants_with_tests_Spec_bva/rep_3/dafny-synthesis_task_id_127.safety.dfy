method {:testEntry} Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := a * b;
}

method {:test} Test11() {
var r0 := Multiply(7721, 102);
expect r0 == 7721 * 102;
}

// REPEAT 3 - TIME: 7.200387 s
