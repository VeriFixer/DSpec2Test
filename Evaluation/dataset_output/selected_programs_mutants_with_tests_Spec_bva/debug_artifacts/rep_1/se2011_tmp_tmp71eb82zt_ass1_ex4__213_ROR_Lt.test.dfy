// se2011_tmp_tmp71eb82zt_ass1_ex4.dfy

method {:testEntry} Eval(x: int) returns (r: int)
  requires x >= 0
  ensures r == x * x
{
  var y: int := x;
  var z: int := 0;
  while y < 0
    invariant 0 <= y <= x && z == x * (x - y)
    decreases y
  {
    z := z + x;
    y := y - 1;
  }
  return z;
}

method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Eval(0);
expect r0 == 0 * 0;
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Eval(100);
expect r0 == 100 * 100;
}
method {:test} Test4() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Eval(10);
expect r0 == 10 * 10;
}

// REPEAT 1 - TIME: 7.8810965 s
