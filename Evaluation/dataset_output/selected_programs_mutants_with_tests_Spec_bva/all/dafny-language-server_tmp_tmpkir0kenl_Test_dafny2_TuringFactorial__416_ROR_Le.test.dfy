// dafny-language-server_tmp_tmpkir0kenl_Test_dafny2_TuringFactorial.dfy

function Factorial(n: nat): nat
{
  if n == 0 then
    1
  else
    n * Factorial(n - 1)
}

method {:testEntry} ComputeFactorial(n: int) returns (u: int)
  requires 1 <= n
  ensures u == Factorial(n)
{
  var r := 1;
  u := 1;
  while r < n
    invariant r <= n
    invariant u == Factorial(r)
  {
    var v, s := u, 1;
    while s <= r + 1
      invariant s <= r + 1
      invariant v == Factorial(r) && u == s * Factorial(r)
    {
      u := u + v;
      s := s + 1;
    }
    r := r + 1;
  }
}


method {:test} Test0() {
expect 1 <= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(2);
expect r0 == Factorial(2);
}
method {:test} Test1() {
expect 1 <= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(1);
expect r0 == Factorial(1);
}
method {:test} Test2() {
expect 1 <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(100);
expect r0 == Factorial(100);
}
method {:test} Test4() {
expect 1 <= 5, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(5);
expect r0 == Factorial(5);
}

// REPEAT 1 - TIME: 7.859793 s

method {:test} Test7() {
expect 1 <= 101, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(101);
expect r0 == Factorial(101);
}

// REPEAT 2 - TIME: 9.0856646 s

method {:test} Test8() {
expect 1 <= 102, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(102);
expect r0 == Factorial(102);
}

// REPEAT 3 - TIME: 10.174829 s

method {:test} Test9() {
expect 1 <= 103, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(103);
expect r0 == Factorial(103);
}

// REPEAT 4 - TIME: 11.1871231 s

method {:test} Test10() {
expect 1 <= 104, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(104);
expect r0 == Factorial(104);
}

// REPEAT 5 - TIME: 12.0863592 s

method {:test} Test11() {
expect 1 <= 105, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(105);
expect r0 == Factorial(105);
}

// REPEAT 6 - TIME: 13.1727609 s

method {:test} Test12() {
expect 1 <= 106, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(106);
expect r0 == Factorial(106);
}

// REPEAT 7 - TIME: 14.2600377 s

method {:test} Test13() {
expect 1 <= 107, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(107);
expect r0 == Factorial(107);
}

// REPEAT 8 - TIME: 15.2612887 s

method {:test} Test14() {
expect 1 <= 108, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(108);
expect r0 == Factorial(108);
}

// REPEAT 9 - TIME: 16.1527918 s

method {:test} Test15() {
expect 1 <= 109, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(109);
expect r0 == Factorial(109);
}

// REPEAT 10 - TIME: 17.0034664 s
