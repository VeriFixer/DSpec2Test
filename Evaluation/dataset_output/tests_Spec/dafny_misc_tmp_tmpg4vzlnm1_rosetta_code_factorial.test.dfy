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

method {:test} Test0() {
var r0 := IterativeFactorial(2);
expect r0 == Factorial(2);
}

// REPEAT 1 - TIME: 2.5824489 s

method {:test} Test1() {
var r0 := IterativeFactorial(3);
expect r0 == Factorial(3);
}

// REPEAT 2 - TIME: 3.3900704 s

method {:test} Test2() {
var r0 := IterativeFactorial(4);
expect r0 == Factorial(4);
}

// REPEAT 3 - TIME: 4.2074004 s

method {:test} Test3() {
var r0 := IterativeFactorial(5);
expect r0 == Factorial(5);
}

// REPEAT 4 - TIME: 5.0963948 s

method {:test} Test4() {
var r0 := IterativeFactorial(6);
expect r0 == Factorial(6);
}

// REPEAT 5 - TIME: 6.2796695 s

method {:test} Test5() {
var r0 := IterativeFactorial(7);
expect r0 == Factorial(7);
}

// REPEAT 6 - TIME: 7.132498 s

method {:test} Test6() {
var r0 := IterativeFactorial(8);
expect r0 == Factorial(8);
}

// REPEAT 7 - TIME: 7.951891 s

method {:test} Test7() {
var r0 := IterativeFactorial(9);
expect r0 == Factorial(9);
}

// REPEAT 8 - TIME: 8.6220022 s

method {:test} Test8() {
var r0 := IterativeFactorial(10);
expect r0 == Factorial(10);
}

// REPEAT 9 - TIME: 9.4030185 s

method {:test} Test9() {
var r0 := IterativeFactorial(11);
expect r0 == Factorial(11);
}

// REPEAT 10 - TIME: 10.0896216 s
