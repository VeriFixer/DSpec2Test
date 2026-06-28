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
  var lastDigit := n;
  fact := Factorial(lastDigit);
}

method {:test} Test5() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(7);
expect r0 == Factorial(7 % 10);
}

// REPEAT 6 - TIME: 6.3204607 s
