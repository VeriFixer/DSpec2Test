// se2011_tmp_tmp71eb82zt_ass1_ex4.dfy

method {:testEntry} Eval(x: int) returns (r: int)
  requires x >= 0
  ensures r == x * x
{
  var y: int := x;
  var z: int := 0;
  while y > 0
    invariant 0 <= y <= x && z == x * (x - y)
    decreases y
  {
    z := z * x;
    y := y - 1;
  }
  return z;
}

method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Eval(1);
expect r0 == 1 * 1;
}

// REPEAT 2 - TIME: 3.7739398 s
