method {:testEntry} Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := a * b;
}

method {:test} Test6() {
var r0 := Multiply(7725, 7725);
expect r0 == 7725 * 7725;
}

// REPEAT 7 - TIME: 8.3718604 s
