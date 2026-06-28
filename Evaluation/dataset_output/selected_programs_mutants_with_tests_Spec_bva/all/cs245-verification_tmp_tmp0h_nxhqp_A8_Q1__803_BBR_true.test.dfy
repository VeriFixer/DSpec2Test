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
  while true
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

method {:test} Test10() {
expect 7889 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(7889, 7720);
expect r0 == power(7720, 7889);
}

// REPEAT 2 - TIME: 11.3430687 s

method {:test} Test11() {
expect 7890 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(7890, 7721);
expect r0 == power(7721, 7890);
}

// REPEAT 3 - TIME: 12.4762788 s

method {:test} Test12() {
expect 7891 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(7891, 7722);
expect r0 == power(7722, 7891);
}

// REPEAT 4 - TIME: 13.5068891 s

method {:test} Test13() {
expect 7892 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(7892, 7723);
expect r0 == power(7723, 7892);
}

// REPEAT 5 - TIME: 14.3600423 s

method {:test} Test14() {
expect 7893 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(7893, 7724);
expect r0 == power(7724, 7893);
}

// REPEAT 6 - TIME: 15.1664157 s

method {:test} Test15() {
expect 7894 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(7894, 7725);
expect r0 == power(7725, 7894);
}

// REPEAT 7 - TIME: 16.2819914 s

method {:test} Test16() {
expect 7895 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(7895, 7726);
expect r0 == power(7726, 7895);
}

// REPEAT 8 - TIME: 17.1900832 s

method {:test} Test17() {
expect 7896 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(7896, 7727);
expect r0 == power(7727, 7896);
}

// REPEAT 9 - TIME: 18.0477525 s

method {:test} Test18() {
expect 7897 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := A8Q1(7897, 7728);
expect r0 == power(7728, 7897);
}

// REPEAT 10 - TIME: 19.0585586 s
