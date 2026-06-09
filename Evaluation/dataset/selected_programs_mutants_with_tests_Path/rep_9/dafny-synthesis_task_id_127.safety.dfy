method {:testEntry} Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := a * b;
}

method {:test} Test8() {
var r0 := Multiply(7727, 7727);
expect r0 == 7727 * 7727;
}

// REPEAT 9 - TIME: 10.9351217 s
