// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Factorial(n: nat): nat
{
  if n == 0 then 1 else n * Factorial(n-1)
}

method {:testEntry} ComputeFactorial(n: int) returns (u: int)
  requires 1 <= n;
  ensures u == Factorial(n);
{
  var r := 1;
  u := 1;
  while (r < n)
    invariant r <= n;
    invariant u == Factorial(r);
  {
    var v, s := u, 1;
    while (s < r + 1)
      invariant s <= r + 1;
      invariant v == Factorial(r) && u == s * Factorial(r);
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

// REPEAT 1 - TIME: 6.2784931 s

method {:test} Test7() {
expect 1 <= 101, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(101);
expect r0 == Factorial(101);
}

// REPEAT 2 - TIME: 7.4865792 s

method {:test} Test8() {
expect 1 <= 102, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(102);
expect r0 == Factorial(102);
}

// REPEAT 3 - TIME: 8.5553288 s

method {:test} Test9() {
expect 1 <= 103, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(103);
expect r0 == Factorial(103);
}

// REPEAT 4 - TIME: 9.3234275 s

method {:test} Test10() {
expect 1 <= 104, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(104);
expect r0 == Factorial(104);
}

// REPEAT 5 - TIME: 10.1041365 s

method {:test} Test11() {
expect 1 <= 105, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(105);
expect r0 == Factorial(105);
}

// REPEAT 6 - TIME: 10.8560979 s

method {:test} Test12() {
expect 1 <= 106, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(106);
expect r0 == Factorial(106);
}

// REPEAT 7 - TIME: 11.522599 s

method {:test} Test13() {
expect 1 <= 107, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(107);
expect r0 == Factorial(107);
}

// REPEAT 8 - TIME: 12.2329298 s

method {:test} Test14() {
expect 1 <= 108, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(108);
expect r0 == Factorial(108);
}

// REPEAT 9 - TIME: 12.844207 s

method {:test} Test15() {
expect 1 <= 109, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(109);
expect r0 == Factorial(109);
}

// REPEAT 10 - TIME: 13.5377215 s
