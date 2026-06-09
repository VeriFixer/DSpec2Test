method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := 2 * x;
  b := 2 * a;
}

method {:test} Test5() {
var r0, r1 := DoubleQuadruple(43);
expect r0 == 2 * 43 && r1 == 4 * 43;
}

// REPEAT 6 - TIME: 6.2631177 s
