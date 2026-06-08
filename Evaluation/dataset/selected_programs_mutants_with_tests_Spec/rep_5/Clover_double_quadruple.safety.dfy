method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := 2 * x;
  b := 2 * a;
}

method {:test} Test4() {
var r0, r1 := DoubleQuadruple(42);
expect r0 == 2 * 42 && r1 == 4 * 42;
}

// REPEAT 5 - TIME: 6.3026509 s
