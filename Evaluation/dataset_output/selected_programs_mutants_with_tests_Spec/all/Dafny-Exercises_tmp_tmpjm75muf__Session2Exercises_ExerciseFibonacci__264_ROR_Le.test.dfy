// Dafny-Exercises_tmp_tmpjm75muf__Session2Exercises_ExerciseFibonacci.dfy

function fib(n: nat): nat
  decreases n
{
  if n == 0 then
    0
  else if n == 1 then
    1
  else
    fib(n - 1) + fib(n - 2)
}

method {:testEntry} fibonacci1(n: nat) returns (f: nat)
  ensures f == fib(n)
{
  var i := 0;
  f := 0;
  var fsig := 1;
  while i <= n
    invariant f == fib(i) && fsig == fib(i + 1)
    invariant i <= n
    decreases n - i
  {
    f, fsig := fsig, f + fsig;
    i := i + 1;
  }
}

method {:testEntry} fibonacci2(n: nat) returns (f: nat)
  ensures f == fib(n)
{
  if n == 0 {
    f := 0;
  } else {
    var i := 1;
    var fant := 0;
    f := 1;
    while i < n
      invariant fant == fib(i - 1) && f == fib(i)
      invariant i <= n
      decreases n - i
    {
      fant, f := f, fant + f;
      i := i + 1;
    }
  }
}

method {:testEntry} fibonacci3(n: nat) returns (f: nat)
  ensures f == fib(n)
{
  {
    var i: int := 0;
    var a := 1;
    f := 0;
    while i < n
      invariant 0 <= i <= n
      invariant if i == 0 then a == fib(i + 1) && f == fib(i) else a == fib(i - 1) && f == fib(i)
      decreases n - i
    {
      a, f := f, a + f;
      i := i + 1;
    }
  }
}


method {:test} Test0() {
var r0 := fibonacci1(1);
expect r0 == fib(1);
}
method {:test} Test1() {
var r0 := fibonacci2(1);
expect r0 == fib(1);
}
method {:test} Test2() {
var r0 := fibonacci3(1);
expect r0 == fib(1);
}

// REPEAT 1 - TIME: 4.1588213 s

method {:test} Test3() {
var r0 := fibonacci1(2);
expect r0 == fib(2);
}
method {:test} Test4() {
var r0 := fibonacci2(2);
expect r0 == fib(2);
}
method {:test} Test5() {
var r0 := fibonacci3(2);
expect r0 == fib(2);
}

// REPEAT 2 - TIME: 6.3266618 s

method {:test} Test6() {
var r0 := fibonacci1(3);
expect r0 == fib(3);
}
method {:test} Test7() {
var r0 := fibonacci2(3);
expect r0 == fib(3);
}
method {:test} Test8() {
var r0 := fibonacci3(3);
expect r0 == fib(3);
}

// REPEAT 3 - TIME: 8.4216282 s

method {:test} Test9() {
var r0 := fibonacci1(2441);
expect r0 == fib(2441);
}
method {:test} Test10() {
var r0 := fibonacci2(2441);
expect r0 == fib(2441);
}
method {:test} Test11() {
var r0 := fibonacci3(2441);
expect r0 == fib(2441);
}

// REPEAT 4 - TIME: 10.2384809 s

method {:test} Test12() {
var r0 := fibonacci1(2442);
expect r0 == fib(2442);
}
method {:test} Test13() {
var r0 := fibonacci2(2442);
expect r0 == fib(2442);
}
method {:test} Test14() {
var r0 := fibonacci3(2442);
expect r0 == fib(2442);
}

// REPEAT 5 - TIME: 11.7569666 s

method {:test} Test15() {
var r0 := fibonacci1(2443);
expect r0 == fib(2443);
}
method {:test} Test16() {
var r0 := fibonacci2(2443);
expect r0 == fib(2443);
}
method {:test} Test17() {
var r0 := fibonacci3(2443);
expect r0 == fib(2443);
}

// REPEAT 6 - TIME: 13.102391 s

method {:test} Test18() {
var r0 := fibonacci1(2444);
expect r0 == fib(2444);
}
method {:test} Test19() {
var r0 := fibonacci2(2444);
expect r0 == fib(2444);
}
method {:test} Test20() {
var r0 := fibonacci3(2444);
expect r0 == fib(2444);
}

// REPEAT 7 - TIME: 14.4070759 s

method {:test} Test21() {
var r0 := fibonacci1(2445);
expect r0 == fib(2445);
}
method {:test} Test22() {
var r0 := fibonacci2(2445);
expect r0 == fib(2445);
}
method {:test} Test23() {
var r0 := fibonacci3(2445);
expect r0 == fib(2445);
}

// REPEAT 8 - TIME: 15.6253049 s

method {:test} Test24() {
var r0 := fibonacci1(2446);
expect r0 == fib(2446);
}
method {:test} Test25() {
var r0 := fibonacci2(2446);
expect r0 == fib(2446);
}
method {:test} Test26() {
var r0 := fibonacci3(2446);
expect r0 == fib(2446);
}

// REPEAT 9 - TIME: 16.9456602 s

method {:test} Test27() {
var r0 := fibonacci1(2447);
expect r0 == fib(2447);
}
method {:test} Test28() {
var r0 := fibonacci2(2447);
expect r0 == fib(2447);
}
method {:test} Test29() {
var r0 := fibonacci3(2447);
expect r0 == fib(2447);
}

// REPEAT 10 - TIME: 18.30705 s
