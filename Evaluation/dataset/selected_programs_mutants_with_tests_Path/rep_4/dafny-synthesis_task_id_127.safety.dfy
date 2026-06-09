method {:testEntry} Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := a * b;
}

method {:test} Test3() {
var r0 := Multiply(7722, 7722);
expect r0 == 7722 * 7722;
}

// REPEAT 4 - TIME: 6.4372076 s
