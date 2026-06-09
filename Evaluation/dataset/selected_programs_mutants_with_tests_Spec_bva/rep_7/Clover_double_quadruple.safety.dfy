method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := 2 * x;
  b := 2 * a;
}

method {:test} Test12() {
var r0, r1 := DoubleQuadruple(106);
expect r0 == 2 * 106 && r1 == 4 * 106;
}

// REPEAT 7 - TIME: 9.1864484 s
