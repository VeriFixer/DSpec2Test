method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := 2 * x;
  b := 2 * a;
}

method {:test} Test6() {
var r0, r1 := DoubleQuadruple(1242);
expect r0 == 2 * 1242 && r1 == 4 * 1242;
}

// REPEAT 7 - TIME: 5.5017402 s
