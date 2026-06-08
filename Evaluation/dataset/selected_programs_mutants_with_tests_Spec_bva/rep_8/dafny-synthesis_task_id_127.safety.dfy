method {:testEntry} Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := a * b;
}

method {:test} Test16() {
var r0 := Multiply(7726, 107);
expect r0 == 7726 * 107;
}

// REPEAT 8 - TIME: 12.1773825 s
