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

method {:test} Test9() {
expect 1 <= 103, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(103);
expect r0 == Factorial(103);
}

// REPEAT 4 - TIME: 9.3234275 s
