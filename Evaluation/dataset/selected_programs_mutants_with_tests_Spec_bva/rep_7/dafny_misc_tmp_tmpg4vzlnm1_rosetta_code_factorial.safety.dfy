// recursive definition of factorial
function Factorial(n: nat): nat {
  if n == 0 then 1 else n * Factorial(n - 1)
}

// iterative implementation of factorial
method {:testEntry} IterativeFactorial(n: nat) returns (result: nat)
  ensures result == Factorial(n)
{
  result := 1;
  var i := 1;
  while i <= n
    invariant i <= n + 1
    invariant result == Factorial(i - 1)
  {
    result := result * i;
    i := i + 1;
  }
}

method {:test} Test11() {
var r0 := IterativeFactorial(106);
expect r0 == Factorial(106);
}

// REPEAT 7 - TIME: 9.9887555 s
