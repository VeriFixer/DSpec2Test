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
  var lastDigit := 10;
  fact := Factorial(lastDigit);
}


method {:test} Test0() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(2);
expect r0 == Factorial(2 % 10);
}

// REPEAT 1 - TIME: 2.5227587 s

method {:test} Test1() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(4);
expect r0 == Factorial(4 % 10);
}

// REPEAT 2 - TIME: 3.3399454 s

method {:test} Test2() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(5);
expect r0 == Factorial(5 % 10);
}

// REPEAT 3 - TIME: 4.0768235 s

method {:test} Test3() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(6);
expect r0 == Factorial(6 % 10);
}

// REPEAT 4 - TIME: 4.8142499 s

method {:test} Test4() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(7);
expect r0 == Factorial(7 % 10);
}

// REPEAT 5 - TIME: 5.7450674 s

method {:test} Test5() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(8);
expect r0 == Factorial(8 % 10);
}

// REPEAT 6 - TIME: 6.5768105 s

method {:test} Test6() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(9);
expect r0 == Factorial(9 % 10);
}

// REPEAT 7 - TIME: 7.2270096 s

method {:test} Test7() {
expect 12 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(12);
expect r0 == Factorial(12 % 10);
}

// REPEAT 8 - TIME: 7.8427172 s

method {:test} Test8() {
expect 13 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(13);
expect r0 == Factorial(13 % 10);
}

// REPEAT 9 - TIME: 8.43618 s

method {:test} Test9() {
expect 14 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(14);
expect r0 == Factorial(14 % 10);
}

// REPEAT 10 - TIME: 9.210491 s
