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
  while false
    invariant z == power(x, y0 - y) && y >= 0
    decreases y
  {
    z := z * x;
    y := y - 1;
  }
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(0, 23);
expect r0 == power(23, 0);
}

// REPEAT 1 - TIME: 6.4603797 s

method {:test} Test1() {
expect 283 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(283, 24);
expect r0 == power(24, 283);
}

// REPEAT 2 - TIME: 10.1330635 s

method {:test} Test2() {
expect 284 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(284, 25);
expect r0 == power(25, 284);
}

// REPEAT 3 - TIME: 13.4572793 s

method {:test} Test3() {
expect 285 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(285, 26);
expect r0 == power(26, 285);
}

// REPEAT 4 - TIME: 16.8336693 s

method {:test} Test4() {
expect 286 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(286, 27);
expect r0 == power(27, 286);
}

// REPEAT 5 - TIME: 20.1985249 s

method {:test} Test5() {
expect 287 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(287, 28);
expect r0 == power(28, 287);
}

// REPEAT 6 - TIME: 23.7316145 s

method {:test} Test6() {
expect 288 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(288, 29);
expect r0 == power(29, 288);
}

// REPEAT 7 - TIME: 26.7939276 s

method {:test} Test7() {
expect 289 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(289, 30);
expect r0 == power(30, 289);
}

// REPEAT 8 - TIME: 30.65925 s

method {:test} Test8() {
expect 290 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(290, 31);
expect r0 == power(31, 290);
}

// REPEAT 9 - TIME: 34.0620192 s

method {:test} Test9() {
expect 291 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(291, 32);
expect r0 == power(32, 291);
}

// REPEAT 10 - TIME: 37.0992354 s
