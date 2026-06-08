method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := 2 * x;
  b := 2 * a;
}

method {:test} Test9() {
var r0, r1 := DoubleQuadruple(1245);
expect r0 == 2 * 1245 && r1 == 4 * 1245;
}

// REPEAT 10 - TIME: 12.1569976 s
