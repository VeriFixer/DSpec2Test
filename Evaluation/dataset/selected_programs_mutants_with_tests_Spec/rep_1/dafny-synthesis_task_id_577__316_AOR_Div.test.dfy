// dafny-synthesis_task_id_577.dfy

function Factorial(n: int): int
  requires n >= 0
  ensures 0 <= Factorial(n)
{
  if n == 0 then
    1
  else
    n * Factorial(n - 1)
}

method {:testEntry} FactorialOfLastDigit(n: int) returns (fact: int)
  requires n >= 0
  ensures fact == Factorial(n % 10)
{
  var lastDigit := n / 10;
  fact := Factorial(lastDigit);
}

method {:test} Test0() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(4);
expect r0 == Factorial(4 % 10);
}

// REPEAT 1 - TIME: 2.4983714 s
