method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := 2 * x;
  b := 2 * a;
}

method {:test} Test15() {
var r0, r1 := DoubleQuadruple(109);
expect r0 == 2 * 109 && r1 == 4 * 109;
}

// REPEAT 10 - TIME: 11.3749048 s
