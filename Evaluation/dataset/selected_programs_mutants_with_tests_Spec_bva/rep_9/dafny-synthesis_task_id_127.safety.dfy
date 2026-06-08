method {:testEntry} Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := a * b;
}

method {:test} Test17() {
var r0 := Multiply(7727, 108);
expect r0 == 7727 * 108;
}

// REPEAT 9 - TIME: 12.7213087 s
