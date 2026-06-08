method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := 2 * x;
  b := 2 * a;
}

method {:test} Test10() {
var r0, r1 := DoubleQuadruple(104);
expect r0 == 2 * 104 && r1 == 4 * 104;
}

// REPEAT 5 - TIME: 8.0556018 s
