// Clover_double_quadruple.dfy

method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  b := 2 * a;
  a := 2 * x;
}

method {:test} Test0() {
var r0, r1 := DoubleQuadruple(1236);
expect r0 == 2 * 1236 && r1 == 4 * 1236;
}

// REPEAT 1 - TIME: 1.843079 s
