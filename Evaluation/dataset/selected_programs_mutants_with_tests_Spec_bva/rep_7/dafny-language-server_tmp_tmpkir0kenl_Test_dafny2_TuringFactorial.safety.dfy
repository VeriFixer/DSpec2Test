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

method {:test} Test12() {
expect 1 <= 106, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(106);
expect r0 == Factorial(106);
}

// REPEAT 7 - TIME: 11.522599 s
