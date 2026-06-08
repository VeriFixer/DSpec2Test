method {:testEntry} Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := a * b;
}

method {:test} Test5() {
var r0 := Multiply(7724, 7724);
expect r0 == 7724 * 7724;
}

// REPEAT 6 - TIME: 8.4765402 s
