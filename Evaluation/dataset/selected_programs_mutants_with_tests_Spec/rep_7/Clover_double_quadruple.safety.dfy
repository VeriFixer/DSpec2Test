method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := 2 * x;
  b := 2 * a;
}

method {:test} Test6() {
var r0, r1 := DoubleQuadruple(44);
expect r0 == 2 * 44 && r1 == 4 * 44;
}

// REPEAT 7 - TIME: 7.6799255 s
