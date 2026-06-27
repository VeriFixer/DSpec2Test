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
  while true
    invariant 0 <= i <= n
    invariant x == Fib(i)
    invariant y == Fib(i + 1)
    decreases n - i
  {
    x, y := y, x + y;
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
var r0 := ComputeFib(0);
expect r0 == Fib(0);
}
method {:test} Test1() {
Teste();
}

// REPEAT 1 - TIME: 4.4317359 s

method {:test} Test2() {
var r0 := ComputeFib(1);
expect r0 == Fib(1);
}

// REPEAT 2 - TIME: 7.2098562 s

method {:test} Test3() {
var r0 := ComputeFib(2);
expect r0 == Fib(2);
}

// REPEAT 3 - TIME: 9.4611352 s

method {:test} Test4() {
var r0 := ComputeFib(3);
expect r0 == Fib(3);
}

// REPEAT 4 - TIME: 11.606135 s

method {:test} Test5() {
var r0 := ComputeFib(1240);
expect r0 == Fib(1240);
}

// REPEAT 5 - TIME: 13.5542239 s

method {:test} Test6() {
var r0 := ComputeFib(1241);
expect r0 == Fib(1241);
}

// REPEAT 6 - TIME: 15.5719349 s

method {:test} Test7() {
var r0 := ComputeFib(1242);
expect r0 == Fib(1242);
}

// REPEAT 7 - TIME: 17.4099438 s

method {:test} Test8() {
var r0 := ComputeFib(1243);
expect r0 == Fib(1243);
}

// REPEAT 8 - TIME: 19.3243819 s

method {:test} Test9() {
var r0 := ComputeFib(1244);
expect r0 == Fib(1244);
}

// REPEAT 9 - TIME: 21.1676185 s

method {:test} Test10() {
var r0 := ComputeFib(1245);
expect r0 == Fib(1245);
}

// REPEAT 10 - TIME: 23.3615686 s
