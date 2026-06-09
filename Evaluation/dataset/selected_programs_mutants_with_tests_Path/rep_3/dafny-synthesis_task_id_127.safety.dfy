method {:testEntry} Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := a * b;
}

method {:test} Test2() {
var r0 := Multiply(7721, 7721);
expect r0 == 7721 * 7721;
}

// REPEAT 3 - TIME: 5.390841 s
