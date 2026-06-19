// dafny_misc_tmp_tmpg4vzlnm1_rosetta_code_factorial.dfy

function Factorial(n: nat): nat
{
  if n == 0 then
    1
  else
    n * Factorial(n - 1)
}

method {:testEntry} IterativeFactorial(n: nat) returns (result: nat)
  ensures result == Factorial(n)
{
  result := 1;
  var i := 1;
  while i >= n
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
method {:test} Test1() {
var r0 := IterativeFactorial(100);
expect r0 == Factorial(100);
}

// REPEAT 1 - TIME: 5.6050882 s

method {:test} Test6() {
var r0 := IterativeFactorial(101);
expect r0 == Factorial(101);
}

// REPEAT 2 - TIME: 6.5500915 s

method {:test} Test7() {
var r0 := IterativeFactorial(102);
expect r0 == Factorial(102);
}

// REPEAT 3 - TIME: 7.4979952 s

method {:test} Test8() {
var r0 := IterativeFactorial(103);
expect r0 == Factorial(103);
}

// REPEAT 4 - TIME: 8.4062842 s

method {:test} Test9() {
var r0 := IterativeFactorial(104);
expect r0 == Factorial(104);
}

// REPEAT 5 - TIME: 9.152015 s

method {:test} Test10() {
var r0 := IterativeFactorial(105);
expect r0 == Factorial(105);
}

// REPEAT 6 - TIME: 9.8065736 s

method {:test} Test11() {
var r0 := IterativeFactorial(106);
expect r0 == Factorial(106);
}

// REPEAT 7 - TIME: 10.489785 s

method {:test} Test12() {
var r0 := IterativeFactorial(107);
expect r0 == Factorial(107);
}

// REPEAT 8 - TIME: 11.2114035 s

method {:test} Test13() {
var r0 := IterativeFactorial(108);
expect r0 == Factorial(108);
}

// REPEAT 9 - TIME: 11.8048327 s

method {:test} Test14() {
var r0 := IterativeFactorial(109);
expect r0 == Factorial(109);
}

// REPEAT 10 - TIME: 12.4579672 s
