// Clover_double_quadruple.dfy

method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := -2 * x;
  b := 2 * a;
}

method {:test} Test1() {
var r0, r1 := DoubleQuadruple(1);
expect r0 == 2 * 1 && r1 == 4 * 1;
}

// REPEAT 2 - TIME: 3.4607432 s
