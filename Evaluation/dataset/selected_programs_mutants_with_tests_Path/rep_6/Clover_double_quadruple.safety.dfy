method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := 2 * x;
  b := 2 * a;
}

method {:test} Test5() {
var r0, r1 := DoubleQuadruple(1241);
expect r0 == 2 * 1241 && r1 == 4 * 1241;
}

// REPEAT 6 - TIME: 8.854686 s
