method {:testEntry} Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := a * b;
}

method {:test} Test7() {
var r0 := Multiply(7726, 7726);
expect r0 == 7726 * 7726;
}

// REPEAT 8 - TIME: 10.1939428 s
