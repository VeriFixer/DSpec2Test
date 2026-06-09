method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := 2 * x;
  b := 2 * a;
}

method {:test} Test9() {
var r0, r1 := DoubleQuadruple(47);
expect r0 == 2 * 47 && r1 == 4 * 47;
}

// REPEAT 10 - TIME: 8.6204224 s
