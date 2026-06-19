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
  var lastDigit := 0;
  fact := Factorial(lastDigit);
}


method {:test} Test0() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(4);
expect r0 == Factorial(4 % 10);
}
method {:test} Test1() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(0);
expect r0 == Factorial(0 % 10);
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(100);
expect r0 == Factorial(100 % 10);
}
method {:test} Test4() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(5);
expect r0 == Factorial(5 % 10);
}
method {:test} Test5() {
expect 62834 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(62834);
expect r0 == Factorial(62834 % 10);
}

// REPEAT 1 - TIME: 6.0549493 s

method {:test} Test7() {
expect 62835 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(62835);
expect r0 == Factorial(62835 % 10);
}

// REPEAT 2 - TIME: 7.175549 s

method {:test} Test8() {
expect 62836 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(62836);
expect r0 == Factorial(62836 % 10);
}

// REPEAT 3 - TIME: 7.9658201 s

method {:test} Test9() {
expect 62837 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(62837);
expect r0 == Factorial(62837 % 10);
}

// REPEAT 4 - TIME: 8.7969536 s

method {:test} Test10() {
expect 62838 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(62838);
expect r0 == Factorial(62838 % 10);
}

// REPEAT 5 - TIME: 9.5369205 s

method {:test} Test11() {
expect 62839 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(62839);
expect r0 == Factorial(62839 % 10);
}

// REPEAT 6 - TIME: 10.2067233 s

method {:test} Test12() {
expect 62842 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(62842);
expect r0 == Factorial(62842 % 10);
}

// REPEAT 7 - TIME: 10.8867625 s

method {:test} Test13() {
expect 62843 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(62843);
expect r0 == Factorial(62843 % 10);
}

// REPEAT 8 - TIME: 11.7208055 s

method {:test} Test14() {
expect 62845 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(62845);
expect r0 == Factorial(62845 % 10);
}

// REPEAT 9 - TIME: 12.5452751 s

method {:test} Test15() {
expect 62846 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(62846);
expect r0 == Factorial(62846 % 10);
}

// REPEAT 10 - TIME: 13.1686907 s
