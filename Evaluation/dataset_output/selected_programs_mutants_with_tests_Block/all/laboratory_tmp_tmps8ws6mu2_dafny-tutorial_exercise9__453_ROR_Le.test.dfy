// laboratory_tmp_tmps8ws6mu2_dafny-tutorial_exercise9.dfy

function fib(n: nat): nat
{
  if n == 0 then
    0
  else if n == 1 then
    1
  else
    fib(n - 1) + fib(n - 2)
}

method {:testEntry} ComputeFib(n: nat) returns (b: nat)
  ensures b == fib(n)
{
  var i: int := 0;
  b := 0;
  var c := 1;
  while i <= n
    invariant 0 <= i <= n
    invariant b == fib(i)
    invariant c == fib(i + 1)
  {
    b, c := c, c + b;
    i := i + 1;
  }
}


method {:test} Test0() {
var r0 := ComputeFib(1);
expect r0 == fib(1);
}

// REPEAT 1 - TIME: 2.3889388 s

method {:test} Test1() {
var r0 := ComputeFib(2);
expect r0 == fib(2);
}

// REPEAT 2 - TIME: 3.5202018 s

method {:test} Test2() {
var r0 := ComputeFib(3);
expect r0 == fib(3);
}

// REPEAT 3 - TIME: 4.5479957 s

method {:test} Test3() {
var r0 := ComputeFib(4);
expect r0 == fib(4);
}

// REPEAT 4 - TIME: 5.4199963 s

method {:test} Test4() {
var r0 := ComputeFib(5);
expect r0 == fib(5);
}

// REPEAT 5 - TIME: 6.434064 s

method {:test} Test5() {
var r0 := ComputeFib(6);
expect r0 == fib(6);
}

// REPEAT 6 - TIME: 7.1991081 s

method {:test} Test6() {
var r0 := ComputeFib(7);
expect r0 == fib(7);
}

// REPEAT 7 - TIME: 7.848045 s

method {:test} Test7() {
var r0 := ComputeFib(8);
expect r0 == fib(8);
}

// REPEAT 8 - TIME: 8.5636855 s

method {:test} Test8() {
var r0 := ComputeFib(9);
expect r0 == fib(9);
}

// REPEAT 9 - TIME: 9.2660057 s

method {:test} Test9() {
var r0 := ComputeFib(10);
expect r0 == fib(10);
}

// REPEAT 10 - TIME: 9.8670818 s
