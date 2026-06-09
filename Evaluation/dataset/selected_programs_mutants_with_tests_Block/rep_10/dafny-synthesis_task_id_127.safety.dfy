method {:testEntry} Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := a * b;
}

method {:test} Test9() {
var r0 := Multiply(7728, 7728);
expect r0 == 7728 * 7728;
}

// REPEAT 10 - TIME: 7.7495422 s
