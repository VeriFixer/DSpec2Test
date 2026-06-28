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
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(2);
expect r0 == Factorial(2 % 10);
}

// REPEAT 1 - TIME: 2.5090647 s

method {:test} Test1() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(3);
expect r0 == Factorial(3 % 10);
}

// REPEAT 2 - TIME: 3.5045159 s

method {:test} Test2() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(4);
expect r0 == Factorial(4 % 10);
}

// REPEAT 3 - TIME: 4.5486085 s

method {:test} Test3() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(5);
expect r0 == Factorial(5 % 10);
}

// REPEAT 4 - TIME: 5.675979 s

method {:test} Test4() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(6);
expect r0 == Factorial(6 % 10);
}

// REPEAT 5 - TIME: 6.7180432 s

method {:test} Test5() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(7);
expect r0 == Factorial(7 % 10);
}

// REPEAT 6 - TIME: 7.5288108 s

method {:test} Test6() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(8);
expect r0 == Factorial(8 % 10);
}

// REPEAT 7 - TIME: 8.3593195 s

method {:test} Test7() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(9);
expect r0 == Factorial(9 % 10);
}

// REPEAT 8 - TIME: 9.1619761 s

method {:test} Test8() {
expect 12 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(12);
expect r0 == Factorial(12 % 10);
}

// REPEAT 9 - TIME: 9.8943186 s

method {:test} Test9() {
expect 13 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(13);
expect r0 == Factorial(13 % 10);
}

// REPEAT 10 - TIME: 10.5939441 s
