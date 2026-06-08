method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := 2 * x;
  b := 2 * a;
}

method {:test} Test8() {
var r0, r1 := DoubleQuadruple(1244);
expect r0 == 2 * 1244 && r1 == 4 * 1244;
}

// REPEAT 9 - TIME: 6.8349985 s
