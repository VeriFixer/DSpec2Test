// cs245-verification_tmp_tmp0h_nxhqp_A8_Q1.dfy

function power(a: int, n: int): int
  requires 0 <= n
  decreases n
{
  if n == 0 then
    1
  else
    a * power(a, n - 1)
}

method {:testEntry} A8Q1(y0: int, x: int) returns (z: int)
  requires y0 >= 0
  ensures z == power(x, y0)
{
  var y := y0;
  z := 1;
  while y > 0
    invariant z == power(x, y0 - y) && y >= 0
    decreases y
  {
    z := z - x;
    y := y - 1;
  }
}

method {:test} Test1() {
expect 283 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(283, 24);
expect r0 == power(24, 283);
}

// REPEAT 2 - TIME: 10.1330635 s
