method {:testEntry} Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := a * b;
}

method {:test} Test10() {
var r0 := Multiply(7720, 101);
expect r0 == 7720 * 101;
}

// REPEAT 2 - TIME: 6.4796867 s
