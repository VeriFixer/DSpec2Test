// Clover_double_quadruple.dfy

method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := -(2 * x);
  b := 2 * a;
}

method {:test} Test0() {
var r0, r1 := DoubleQuadruple(0);
expect r0 == 2 * 0 && r1 == 4 * 0;
}
method {:test} Test1() {
var r0, r1 := DoubleQuadruple(-100);
expect r0 == 2 * -100 && r1 == 4 * -100;
}
method {:test} Test2() {
var r0, r1 := DoubleQuadruple(100);
expect r0 == 2 * 100 && r1 == 4 * 100;
}

// REPEAT 1 - TIME: 5.1840242 s
