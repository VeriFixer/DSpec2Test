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
  var lastDigit := n + 10;
  fact := Factorial(lastDigit);
}


method {:test} Test0() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(4);
expect r0 == Factorial(4 % 10);
}

// REPEAT 1 - TIME: 2.6682029 s

method {:test} Test1() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(5);
expect r0 == Factorial(5 % 10);
}

// REPEAT 2 - TIME: 3.4811439 s

method {:test} Test2() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(6);
expect r0 == Factorial(6 % 10);
}

// REPEAT 3 - TIME: 4.3784401 s

method {:test} Test3() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(7);
expect r0 == Factorial(7 % 10);
}

// REPEAT 4 - TIME: 5.2919895 s

method {:test} Test4() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(8);
expect r0 == Factorial(8 % 10);
}

// REPEAT 5 - TIME: 6.1504424 s

method {:test} Test5() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(9);
expect r0 == Factorial(9 % 10);
}

// REPEAT 6 - TIME: 7.1618728 s

method {:test} Test6() {
expect 14 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(14);
expect r0 == Factorial(14 % 10);
}

// REPEAT 7 - TIME: 7.8567337 s

method {:test} Test7() {
expect 15 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(15);
expect r0 == Factorial(15 % 10);
}

// REPEAT 8 - TIME: 8.6386303 s

method {:test} Test8() {
expect 16 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(16);
expect r0 == Factorial(16 % 10);
}

// REPEAT 9 - TIME: 9.2778698 s

method {:test} Test9() {
expect 17 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(17);
expect r0 == Factorial(17 % 10);
}

// REPEAT 10 - TIME: 9.8548714 s
