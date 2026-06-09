method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := 2 * x;
  b := 2 * a;
}

method {:test} Test13() {
var r0, r1 := DoubleQuadruple(107);
expect r0 == 2 * 107 && r1 == 4 * 107;
}

// REPEAT 8 - TIME: 9.7900616 s
