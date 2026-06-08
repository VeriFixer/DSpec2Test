method {:testEntry} Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := a * b;
}

method {:test} Test13() {
var r0 := Multiply(7723, 104);
expect r0 == 7723 * 104;
}

// REPEAT 5 - TIME: 10.0392499 s
