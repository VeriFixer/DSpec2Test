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

// REPEAT 1 - TIME: 2.5359661 s

method {:test} Test2() {
expect 1 <= 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(3);
expect r0 == Factorial(3);
}

// REPEAT 2 - TIME: 3.5625631 s

method {:test} Test4() {
expect 1 <= 4, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(4);
expect r0 == Factorial(4);
}

// REPEAT 3 - TIME: 4.537563 s

method {:test} Test6() {
expect 1 <= 5, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(5);
expect r0 == Factorial(5);
}

// REPEAT 4 - TIME: 5.6436414 s

method {:test} Test8() {
expect 1 <= 6, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(6);
expect r0 == Factorial(6);
}

// REPEAT 5 - TIME: 6.7944469 s

method {:test} Test10() {
expect 1 <= 7, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(7);
expect r0 == Factorial(7);
}

// REPEAT 6 - TIME: 7.7318138 s

method {:test} Test12() {
expect 1 <= 8, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(8);
expect r0 == Factorial(8);
}

// REPEAT 7 - TIME: 8.6858674 s

method {:test} Test14() {
expect 1 <= 9, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(9);
expect r0 == Factorial(9);
}

// REPEAT 8 - TIME: 9.5171818 s

method {:test} Test16() {
expect 1 <= 10, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(10);
expect r0 == Factorial(10);
}

// REPEAT 9 - TIME: 10.3082964 s

method {:test} Test18() {
expect 1 <= 11, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(11);
expect r0 == Factorial(11);
}

// REPEAT 10 - TIME: 11.1663425 s
