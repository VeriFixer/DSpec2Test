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
  while false
    invariant r <= n
    invariant u == Factorial(r)
  {
    var v, s := u, 1;
    while s < r + 1
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

// REPEAT 1 - TIME: 2.8284126 s
