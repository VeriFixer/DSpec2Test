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
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(1, 7719);
expect r0 == power(7719, 1);
}

// REPEAT 1 - TIME: 2.5789126 s

method {:test} Test1() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(2, 7720);
expect r0 == power(7720, 2);
}

// REPEAT 2 - TIME: 3.5971345 s

method {:test} Test2() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(3, 7721);
expect r0 == power(7721, 3);
}

// REPEAT 3 - TIME: 4.3480149 s

method {:test} Test3() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(4, 7722);
expect r0 == power(7722, 4);
}

// REPEAT 4 - TIME: 5.1526143 s

method {:test} Test4() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(5, 7723);
expect r0 == power(7723, 5);
}

// REPEAT 5 - TIME: 5.863918 s

method {:test} Test5() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(6, 7724);
expect r0 == power(7724, 6);
}

// REPEAT 6 - TIME: 6.554737 s

method {:test} Test6() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(7, 7725);
expect r0 == power(7725, 7);
}

// REPEAT 7 - TIME: 7.233648 s

method {:test} Test7() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(8, 7726);
expect r0 == power(7726, 8);
}

// REPEAT 8 - TIME: 7.9611443 s

method {:test} Test8() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(9, 7727);
expect r0 == power(7727, 9);
}

// REPEAT 9 - TIME: 8.6551541 s

method {:test} Test9() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(10, 7728);
expect r0 == power(7728, 10);
}

// REPEAT 10 - TIME: 9.2641267 s
