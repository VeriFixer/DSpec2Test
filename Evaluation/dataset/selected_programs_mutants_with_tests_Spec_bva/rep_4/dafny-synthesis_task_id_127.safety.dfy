method {:testEntry} Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := a * b;
}

method {:test} Test12() {
var r0 := Multiply(7722, 103);
expect r0 == 7722 * 103;
}

// REPEAT 4 - TIME: 9.3120072 s
