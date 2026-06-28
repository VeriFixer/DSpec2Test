// Metodos_Formais_tmp_tmpbez22nnn_Aula_4_ex3.dfy

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

method {:testEntry} Teste()
{
  var n := 3;
  var f := ComputeFib(n);
  assert f == 2;
}


method {:test} Test0() {
var r0 := ComputeFib(1);
expect r0 == Fib(1);
}
method {:test} Test1() {
Teste();
}

// REPEAT 1 - TIME: 2.6530726 s

method {:test} Test2() {
var r0 := ComputeFib(2);
expect r0 == Fib(2);
}

// REPEAT 2 - TIME: 3.5167203 s

method {:test} Test3() {
var r0 := ComputeFib(3);
expect r0 == Fib(3);
}

// REPEAT 3 - TIME: 4.2713886 s

method {:test} Test4() {
var r0 := ComputeFib(4);
expect r0 == Fib(4);
}

// REPEAT 4 - TIME: 4.9972802 s

method {:test} Test5() {
var r0 := ComputeFib(5);
expect r0 == Fib(5);
}

// REPEAT 5 - TIME: 5.8495208 s

method {:test} Test6() {
var r0 := ComputeFib(6);
expect r0 == Fib(6);
}

// REPEAT 6 - TIME: 6.7391895 s

method {:test} Test7() {
var r0 := ComputeFib(7);
expect r0 == Fib(7);
}

// REPEAT 7 - TIME: 7.6773575 s

method {:test} Test8() {
var r0 := ComputeFib(8);
expect r0 == Fib(8);
}

// REPEAT 8 - TIME: 8.5328902 s

method {:test} Test9() {
var r0 := ComputeFib(9);
expect r0 == Fib(9);
}

// REPEAT 9 - TIME: 9.1848694 s

method {:test} Test10() {
var r0 := ComputeFib(10);
expect r0 == Fib(10);
}

// REPEAT 10 - TIME: 9.8090682 s
