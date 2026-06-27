// Programmverifikation-und-synthese_tmp_tmppurk6ime_PVS_Assignment_ex_05_Hoangkim_ex_05_Hoangkim.dfy

function fib(n: nat): nat
{
  if n < 2 then
    n
  else
    fib(n - 2) + fib(n - 1)
}

method {:testEntry} fibIter(n: nat) returns (a: nat)
  requires n > 0
  ensures a == fib(n)
{
  a := 0;
  var b, x := 1, 0;
  while x == n
    invariant 0 <= x <= n
    invariant a == fib(x)
    invariant b == fib(x + 1)
  {
    a, b := b, a + b;
    x := x + 1;
  }
  assert a == fib(n);
}

function fact(n: nat): nat
{
  if n == 0 then
    1
  else
    n * fact(n - 1)
}

method {:testEntry} factIter(n: nat) returns (a: nat)
  requires n >= 0
  ensures a == fact(n)
{
  a := 1;
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant a == fact(i - 1)
  {
    a := a * i;
    i := i + 1;
  }
  assert a == fact(n);
}

function gcd(m: nat, n: nat): nat
  requires m > 0 && n > 0
{
  if m == n then
    m
  else if m > n then
    gcd(m - n, n)
  else
    gcd(m, n - m)
}

method {:testEntry} gcdI(m: int, n: int) returns (g: int)
  requires m > 0 && n > 0
  ensures g == gcd(m, n)
{
  var x: int;
  g := m;
  x := n;
  while g != x
    invariant x > 0
    invariant g > 0
    invariant gcd(g, x) == gcd(m, n)
    decreases x + g
  {
    if g > x {
      g := g - x;
    } else {
      x := x - g;
    }
  }
}


method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(1);
expect r0 == fib(1);
}
method {:test} Test1() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(2);
expect r0 == fact(2);
}
method {:test} Test2() {
expect 11844 > 0 && 5922 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(11844, 5922);
expect r0 == gcd(11844, 5922);
}
method {:test} Test3() {
expect 16476 > 0 && 18386 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16476, 18386);
expect r0 == gcd(16476, 18386);
}

// REPEAT 1 - TIME: 5.0246229 s

method {:test} Test4() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(2);
expect r0 == fib(2);
}
method {:test} Test5() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(3);
expect r0 == fact(3);
}
method {:test} Test6() {
expect 38011 > 0 && 18387 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(38011, 18387);
expect r0 == gcd(38011, 18387);
}
method {:test} Test7() {
expect 42628 > 0 && 18387 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(42628, 18387);
expect r0 == gcd(42628, 18387);
}

// REPEAT 2 - TIME: 7.987973 s

method {:test} Test8() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(3);
expect r0 == fib(3);
}
method {:test} Test9() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(4);
expect r0 == fact(4);
}
method {:test} Test10() {
expect 42629 > 0 && 18388 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(42629, 18388);
expect r0 == gcd(42629, 18388);
}

// REPEAT 3 - TIME: 10.672508 s

method {:test} Test12() {
expect 8949 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(8949);
expect r0 == fib(8949);
}
method {:test} Test13() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(5);
expect r0 == fact(5);
}
method {:test} Test14() {
expect 42630 > 0 && 18389 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(42630, 18389);
expect r0 == gcd(42630, 18389);
}

// REPEAT 4 - TIME: 13.2833401 s

method {:test} Test16() {
expect 8950 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(8950);
expect r0 == fib(8950);
}
method {:test} Test17() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(6);
expect r0 == fact(6);
}
method {:test} Test18() {
expect 43702 > 0 && 21851 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(43702, 21851);
expect r0 == gcd(43702, 21851);
}
method {:test} Test19() {
expect 44916 > 0 && 22458 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(44916, 22458);
expect r0 == gcd(44916, 22458);
}

// REPEAT 5 - TIME: 15.5244082 s

method {:test} Test20() {
expect 8951 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(8951);
expect r0 == fib(8951);
}
method {:test} Test21() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(7);
expect r0 == fact(7);
}
method {:test} Test22() {
expect 46155 > 0 && 22459 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(46155, 22459);
expect r0 == gcd(46155, 22459);
}

// REPEAT 6 - TIME: 17.5726544 s

method {:test} Test24() {
expect 8952 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(8952);
expect r0 == fib(8952);
}
method {:test} Test25() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(8);
expect r0 == fact(8);
}
method {:test} Test26() {
expect 46156 > 0 && 22460 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(46156, 22460);
expect r0 == gcd(46156, 22460);
}
method {:test} Test27() {
expect 48440 > 0 && 24220 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(48440, 24220);
expect r0 == gcd(48440, 24220);
}

// REPEAT 7 - TIME: 19.1750842 s

method {:test} Test28() {
expect 8953 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(8953);
expect r0 == fib(8953);
}
method {:test} Test29() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(9);
expect r0 == fact(9);
}
method {:test} Test30() {
expect 48442 > 0 && 24221 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(48442, 24221);
expect r0 == gcd(48442, 24221);
}
method {:test} Test31() {
expect 50880 > 0 && 24221 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(50880, 24221);
expect r0 == gcd(50880, 24221);
}

// REPEAT 8 - TIME: 21.328028 s

method {:test} Test32() {
expect 8954 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(8954);
expect r0 == fib(8954);
}
method {:test} Test33() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(10);
expect r0 == fact(10);
}
method {:test} Test34() {
expect 50881 > 0 && 24222 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(50881, 24222);
expect r0 == gcd(50881, 24222);
}
method {:test} Test35() {
expect 50881 > 0 && 101226 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(50881, 101226);
expect r0 == gcd(50881, 101226);
}

// REPEAT 9 - TIME: 23.6434387 s

method {:test} Test36() {
expect 8955 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(8955);
expect r0 == fib(8955);
}
method {:test} Test37() {
expect 11 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(11);
expect r0 == fact(11);
}
method {:test} Test38() {
expect 217892 > 0 && 108946 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(217892, 108946);
expect r0 == gcd(217892, 108946);
}
method {:test} Test39() {
expect 202454 > 0 && 101227 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(202454, 101227);
expect r0 == gcd(202454, 101227);
}

// REPEAT 10 - TIME: 25.782583 s
