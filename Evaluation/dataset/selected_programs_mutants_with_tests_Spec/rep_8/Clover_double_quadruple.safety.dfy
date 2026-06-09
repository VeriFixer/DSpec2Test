method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := 2 * x;
  b := 2 * a;
}

method {:test} Test7() {
var r0, r1 := DoubleQuadruple(45);
expect r0 == 2 * 45 && r1 == 4 * 45;
}

// REPEAT 8 - TIME: 7.4898796 s
