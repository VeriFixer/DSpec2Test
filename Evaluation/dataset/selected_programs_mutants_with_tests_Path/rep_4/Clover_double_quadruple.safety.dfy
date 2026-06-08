method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := 2 * x;
  b := 2 * a;
}

method {:test} Test3() {
var r0, r1 := DoubleQuadruple(1239);
expect r0 == 2 * 1239 && r1 == 4 * 1239;
}

// REPEAT 4 - TIME: 6.8400871 s
