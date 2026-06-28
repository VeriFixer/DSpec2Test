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
  while x < n
    invariant 0 <= x <= n
    invariant a == fib(x)
    invariant b == fib(x + 1)
  {
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

// REPEAT 1 - TIME: 5.1455765 s

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
expect 39212 > 0 && 18387 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(39212, 18387);
expect r0 == gcd(39212, 18387);
}

// REPEAT 2 - TIME: 8.5160551 s

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
expect 39776 > 0 && 19888 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(39776, 19888);
expect r0 == gcd(39776, 19888);
}
method {:test} Test11() {
expect 39213 > 0 && 18388 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(39213, 18388);
expect r0 == gcd(39213, 18388);
}

// REPEAT 3 - TIME: 11.1590652 s

method {:test} Test12() {
expect 285 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(285);
expect r0 == fib(285);
}
method {:test} Test13() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(5);
expect r0 == fact(5);
}
method {:test} Test14() {
expect 41015 > 0 && 19889 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(41015, 19889);
expect r0 == gcd(41015, 19889);
}
method {:test} Test15() {
expect 57488 > 0 && 28744 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(57488, 28744);
expect r0 == gcd(57488, 28744);
}

// REPEAT 4 - TIME: 13.5755465 s

method {:test} Test16() {
expect 286 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(286);
expect r0 == fib(286);
}
method {:test} Test17() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(6);
expect r0 == fact(6);
}
method {:test} Test18() {
expect 58727 > 0 && 28745 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(58727, 28745);
expect r0 == gcd(58727, 28745);
}
method {:test} Test19() {
expect 57490 > 0 && 28745 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(57490, 28745);
expect r0 == gcd(57490, 28745);
}

// REPEAT 5 - TIME: 16.2367406 s

method {:test} Test20() {
expect 287 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(287);
expect r0 == fib(287);
}
method {:test} Test21() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(7);
expect r0 == fact(7);
}
method {:test} Test22() {
expect 59798 > 0 && 29899 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(59798, 29899);
expect r0 == gcd(59798, 29899);
}
method {:test} Test23() {
expect 58728 > 0 && 28746 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(58728, 28746);
expect r0 == gcd(58728, 28746);
}

// REPEAT 6 - TIME: 18.2269202 s

method {:test} Test24() {
expect 288 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(288);
expect r0 == fib(288);
}
method {:test} Test25() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(8);
expect r0 == fact(8);
}
method {:test} Test26() {
expect 61037 > 0 && 29900 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(61037, 29900);
expect r0 == gcd(61037, 29900);
}
method {:test} Test27() {
expect 59800 > 0 && 29900 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(59800, 29900);
expect r0 == gcd(59800, 29900);
}

// REPEAT 7 - TIME: 20.3411168 s

method {:test} Test28() {
expect 289 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(289);
expect r0 == fib(289);
}
method {:test} Test29() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(9);
expect r0 == fact(9);
}
method {:test} Test30() {
expect 61038 > 0 && 29901 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(61038, 29901);
expect r0 == gcd(61038, 29901);
}
method {:test} Test31() {
expect 62108 > 0 && 31054 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(62108, 31054);
expect r0 == gcd(62108, 31054);
}

// REPEAT 8 - TIME: 22.6063218 s

method {:test} Test32() {
expect 290 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(290);
expect r0 == fib(290);
}
method {:test} Test33() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(10);
expect r0 == fact(10);
}
method {:test} Test34() {
expect 62110 > 0 && 31055 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(62110, 31055);
expect r0 == gcd(62110, 31055);
}
method {:test} Test35() {
expect 63347 > 0 && 31055 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(63347, 31055);
expect r0 == gcd(63347, 31055);
}

// REPEAT 9 - TIME: 25.0492452 s

method {:test} Test36() {
expect 291 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(291);
expect r0 == fib(291);
}
method {:test} Test37() {
expect 11 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(11);
expect r0 == fact(11);
}
method {:test} Test38() {
expect 63348 > 0 && 31056 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(63348, 31056);
expect r0 == gcd(63348, 31056);
}

// REPEAT 10 - TIME: 27.2902527 s
