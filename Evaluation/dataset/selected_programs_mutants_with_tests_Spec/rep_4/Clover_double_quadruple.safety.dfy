method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := 2 * x;
  b := 2 * a;
}

method {:test} Test3() {
var r0, r1 := DoubleQuadruple(41);
expect r0 == 2 * 41 && r1 == 4 * 41;
}

// REPEAT 4 - TIME: 5.4454788 s
