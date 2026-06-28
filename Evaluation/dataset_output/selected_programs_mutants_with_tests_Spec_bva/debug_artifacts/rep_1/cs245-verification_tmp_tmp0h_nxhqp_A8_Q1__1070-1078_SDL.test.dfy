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
    y := y - 1;
  }
}

method {:test} Test0() {
expect 4681 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(4681, 7719);
expect r0 == power(7719, 4681);
}
method {:test} Test1() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(0, 23);
expect r0 == power(23, 0);
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(100, 0);
expect r0 == power(0, 100);
}
method {:test} Test3() {
expect 2439 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(2439, -100);
expect r0 == power(-100, 2439);
}
method {:test} Test4() {
expect 2439 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(2439, 100);
expect r0 == power(100, 2439);
}
method {:test} Test5() {
expect 5922 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(5922, 0);
expect r0 == power(0, 5922);
}
method {:test} Test6() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(2, 1);
expect r0 == power(1, 2);
}
method {:test} Test7() {
expect 7888 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(7888, 1);
expect r0 == power(1, 7888);
}

// REPEAT 1 - TIME: 10.2734631 s
