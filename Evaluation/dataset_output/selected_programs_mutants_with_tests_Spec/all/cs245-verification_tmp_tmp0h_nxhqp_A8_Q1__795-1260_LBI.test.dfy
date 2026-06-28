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
    break;
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

method {:test} Test1() {
expect 4682 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(4682, 7720);
expect r0 == power(7720, 4682);
}

// REPEAT 2 - TIME: 4.5228878 s

method {:test} Test2() {
expect 4683 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(4683, 7721);
expect r0 == power(7721, 4683);
}

// REPEAT 3 - TIME: 5.6176194 s

method {:test} Test3() {
expect 4684 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(4684, 7722);
expect r0 == power(7722, 4684);
}

// REPEAT 4 - TIME: 6.7408481 s

method {:test} Test4() {
expect 4685 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(4685, 7723);
expect r0 == power(7723, 4685);
}

// REPEAT 5 - TIME: 7.8935781 s

method {:test} Test5() {
expect 4686 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(4686, 7724);
expect r0 == power(7724, 4686);
}

// REPEAT 6 - TIME: 8.812151 s

method {:test} Test6() {
expect 4687 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(4687, 7725);
expect r0 == power(7725, 4687);
}

// REPEAT 7 - TIME: 9.6456264 s

method {:test} Test7() {
expect 4688 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(4688, 7726);
expect r0 == power(7726, 4688);
}

// REPEAT 8 - TIME: 10.5533804 s

method {:test} Test8() {
expect 4689 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(4689, 7727);
expect r0 == power(7727, 4689);
}

// REPEAT 9 - TIME: 11.4058784 s

method {:test} Test9() {
expect 4690 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(4690, 7728);
expect r0 == power(7728, 4690);
}

// REPEAT 10 - TIME: 12.1272985 s
