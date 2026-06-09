method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := 2 * x;
  b := 2 * a;
}

method {:test} Test7() {
var r0, r1 := DoubleQuadruple(1243);
expect r0 == 2 * 1243 && r1 == 4 * 1243;
}

// REPEAT 8 - TIME: 6.0261441 s
