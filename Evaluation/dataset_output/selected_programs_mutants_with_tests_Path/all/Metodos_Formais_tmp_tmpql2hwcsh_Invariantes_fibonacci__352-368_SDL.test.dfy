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
    i := i + 1;
  }
}


method {:test} Test0() {
var r0 := ComputeFib(0);
expect r0 == Fib(0);
}

// REPEAT 1 - TIME: 5.8046936 s

method {:test} Test1() {
var r0 := ComputeFib(1);
expect r0 == Fib(1);
}

// REPEAT 2 - TIME: 9.4900097 s

method {:test} Test2() {
var r0 := ComputeFib(2);
expect r0 == Fib(2);
}

// REPEAT 3 - TIME: 12.7149876 s

method {:test} Test3() {
var r0 := ComputeFib(3);
expect r0 == Fib(3);
}

// REPEAT 4 - TIME: 16.1353159 s

method {:test} Test4() {
var r0 := ComputeFib(1240);
expect r0 == Fib(1240);
}

// REPEAT 5 - TIME: 19.1784009 s

method {:test} Test5() {
var r0 := ComputeFib(1241);
expect r0 == Fib(1241);
}

// REPEAT 6 - TIME: 22.4232415 s

method {:test} Test6() {
var r0 := ComputeFib(1242);
expect r0 == Fib(1242);
}

// REPEAT 7 - TIME: 25.377175 s

method {:test} Test7() {
var r0 := ComputeFib(1243);
expect r0 == Fib(1243);
}

// REPEAT 8 - TIME: 28.8469836 s

method {:test} Test8() {
var r0 := ComputeFib(1244);
expect r0 == Fib(1244);
}

// REPEAT 9 - TIME: 32.667753 s

method {:test} Test9() {
var r0 := ComputeFib(1245);
expect r0 == Fib(1245);
}

// REPEAT 10 - TIME: 36.2147813 s
