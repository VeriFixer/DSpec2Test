method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := 2 * x;
  b := 2 * a;
}

method {:test} Test2() {
var r0, r1 := DoubleQuadruple(40);
expect r0 == 2 * 40 && r1 == 4 * 40;
}

// REPEAT 3 - TIME: 4.5421273 s
