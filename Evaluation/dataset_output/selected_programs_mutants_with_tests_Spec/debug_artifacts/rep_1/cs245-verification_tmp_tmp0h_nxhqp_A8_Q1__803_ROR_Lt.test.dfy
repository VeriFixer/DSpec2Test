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
  while y < 0
    invariant z == power(x, y0 - y) && y >= 0
    decreases y
  {
    z := z * x;
    y := y - 1;
  }
}

method {:test} Test0() {
expect 4681 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(4681, 7719);
expect r0 == power(7719, 4681);
}

// REPEAT 1 - TIME: 3.4329851 s
