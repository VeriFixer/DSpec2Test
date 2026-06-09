method {:testEntry} Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := a * b;
}

method {:test} Test4() {
var r0 := Multiply(7723, 7723);
expect r0 == 7723 * 7723;
}

// REPEAT 5 - TIME: 4.7301154 s
