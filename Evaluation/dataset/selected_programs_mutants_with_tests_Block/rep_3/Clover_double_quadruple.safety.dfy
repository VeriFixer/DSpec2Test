method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := 2 * x;
  b := 2 * a;
}

method {:test} Test2() {
var r0, r1 := DoubleQuadruple(1238);
expect r0 == 2 * 1238 && r1 == 4 * 1238;
}

// REPEAT 3 - TIME: 2.9916211 s
