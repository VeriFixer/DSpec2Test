method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := 2 * x;
  b := 2 * a;
}

method {:test} Test4() {
var r0, r1 := DoubleQuadruple(1240);
expect r0 == 2 * 1240 && r1 == 4 * 1240;
}

// REPEAT 5 - TIME: 4.1525492 s
