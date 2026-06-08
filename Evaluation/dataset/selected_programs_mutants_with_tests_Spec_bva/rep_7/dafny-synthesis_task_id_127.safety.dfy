method {:testEntry} Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := a * b;
}

method {:test} Test15() {
var r0 := Multiply(7725, 106);
expect r0 == 7725 * 106;
}

// REPEAT 7 - TIME: 11.4906921 s
