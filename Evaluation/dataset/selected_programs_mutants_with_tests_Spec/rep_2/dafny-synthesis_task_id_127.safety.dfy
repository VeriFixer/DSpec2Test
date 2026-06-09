method {:testEntry} Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := a * b;
}

method {:test} Test1() {
var r0 := Multiply(7720, 1);
expect r0 == 7720 * 1;
}

// REPEAT 2 - TIME: 3.2058902 s
