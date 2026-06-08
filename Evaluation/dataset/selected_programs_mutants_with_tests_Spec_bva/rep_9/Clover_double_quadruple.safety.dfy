method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := 2 * x;
  b := 2 * a;
}

method {:test} Test14() {
var r0, r1 := DoubleQuadruple(108);
expect r0 == 2 * 108 && r1 == 4 * 108;
}

// REPEAT 9 - TIME: 10.8090855 s
