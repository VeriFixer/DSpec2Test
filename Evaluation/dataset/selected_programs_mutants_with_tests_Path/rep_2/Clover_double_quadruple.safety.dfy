method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := 2 * x;
  b := 2 * a;
}

method {:test} Test1() {
var r0, r1 := DoubleQuadruple(1237);
expect r0 == 2 * 1237 && r1 == 4 * 1237;
}

// REPEAT 2 - TIME: 4.5588836 s
