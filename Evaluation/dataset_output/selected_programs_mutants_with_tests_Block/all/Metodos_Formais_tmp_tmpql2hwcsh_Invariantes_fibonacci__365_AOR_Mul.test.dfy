// Metodos_Formais_tmp_tmpql2hwcsh_Invariantes_fibonacci.dfy

function Fib(n: nat): nat
{
  if n < 2 then
    n
  else
    Fib(n - 2) + Fib(n - 1)
}

method {:testEntry} ComputeFib(n: nat) returns (x: nat)
  ensures x == Fib(n)
{
  var i := 0;
  x := 0;
  var y := 1;
  while i < n
    invariant 0 <= i <= n
    invariant x == Fib(i)
    invariant y == Fib(i + 1)
    decreases n - i
  {
    x, y := y, x * y;
    i := i + 1;
  }
}


method {:test} Test0() {
var r0 := ComputeFib(1);
expect r0 == Fib(1);
}

// REPEAT 1 - TIME: 2.2142649 s

method {:test} Test1() {
var r0 := ComputeFib(2);
expect r0 == Fib(2);
}

// REPEAT 2 - TIME: 3.01399 s

method {:test} Test2() {
var r0 := ComputeFib(3);
expect r0 == Fib(3);
}

// REPEAT 3 - TIME: 3.8157321 s

method {:test} Test3() {
var r0 := ComputeFib(4);
expect r0 == Fib(4);
}

// REPEAT 4 - TIME: 4.583941 s

method {:test} Test4() {
var r0 := ComputeFib(5);
expect r0 == Fib(5);
}

// REPEAT 5 - TIME: 5.3626223 s

method {:test} Test5() {
var r0 := ComputeFib(6);
expect r0 == Fib(6);
}

// REPEAT 6 - TIME: 6.225577 s

method {:test} Test6() {
var r0 := ComputeFib(7);
expect r0 == Fib(7);
}

// REPEAT 7 - TIME: 7.2100843 s

method {:test} Test7() {
var r0 := ComputeFib(8);
expect r0 == Fib(8);
}

// REPEAT 8 - TIME: 7.9128753 s

method {:test} Test8() {
var r0 := ComputeFib(9);
expect r0 == Fib(9);
}

// REPEAT 9 - TIME: 8.5537327 s

method {:test} Test9() {
var r0 := ComputeFib(10);
expect r0 == Fib(10);
}

// REPEAT 10 - TIME: 9.2150048 s
