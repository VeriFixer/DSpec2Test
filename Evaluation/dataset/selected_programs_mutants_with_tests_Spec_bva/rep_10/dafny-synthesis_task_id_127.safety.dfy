method {:testEntry} Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := a * b;
}

method {:test} Test18() {
var r0 := Multiply(7728, 109);
expect r0 == 7728 * 109;
}

// REPEAT 10 - TIME: 13.4384121 s
