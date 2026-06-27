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
  while false
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

// REPEAT 1 - TIME: 2.7917059 s

method {:test} Test1() {
var r0 := ComputeFib(2);
expect r0 == fib(2);
}

// REPEAT 2 - TIME: 3.8264396 s

method {:test} Test2() {
var r0 := ComputeFib(3);
expect r0 == fib(3);
}

// REPEAT 3 - TIME: 4.7157888 s

method {:test} Test3() {
var r0 := ComputeFib(2441);
expect r0 == fib(2441);
}

// REPEAT 4 - TIME: 5.5650728 s

method {:test} Test4() {
var r0 := ComputeFib(2442);
expect r0 == fib(2442);
}

// REPEAT 5 - TIME: 6.6572111 s

method {:test} Test5() {
var r0 := ComputeFib(2443);
expect r0 == fib(2443);
}

// REPEAT 6 - TIME: 7.540187 s

method {:test} Test6() {
var r0 := ComputeFib(2444);
expect r0 == fib(2444);
}

// REPEAT 7 - TIME: 8.3469267 s

method {:test} Test7() {
var r0 := ComputeFib(2445);
expect r0 == fib(2445);
}

// REPEAT 8 - TIME: 9.0556302 s

method {:test} Test8() {
var r0 := ComputeFib(2446);
expect r0 == fib(2446);
}

// REPEAT 9 - TIME: 9.6570916 s

method {:test} Test9() {
var r0 := ComputeFib(2447);
expect r0 == fib(2447);
}

// REPEAT 10 - TIME: 10.36815 s
