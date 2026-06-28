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
  while true
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
expect 1 > 0 && 452 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(1, 452);
expect r0 == gcd(1, 452);
}

// REPEAT 1 - TIME: 11.019924 s

method {:test} Test3() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(2);
expect r0 == fib(2);
}
method {:test} Test4() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(3);
expect r0 == fact(3);
}
method {:test} Test5() {
expect 2 > 0 && 453 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(2, 453);
expect r0 == gcd(2, 453);
}

// REPEAT 2 - TIME: 18.8963595 s

method {:test} Test6() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(3);
expect r0 == fib(3);
}
method {:test} Test7() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(4);
expect r0 == fact(4);
}
method {:test} Test8() {
expect 3 > 0 && 454 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(3, 454);
expect r0 == gcd(3, 454);
}

// REPEAT 3 - TIME: 28.0078249 s

method {:test} Test9() {
expect 978 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(978);
expect r0 == fib(978);
}
method {:test} Test10() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(5);
expect r0 == fact(5);
}
method {:test} Test11() {
expect 7947 > 0 && 15894 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(7947, 15894);
expect r0 == gcd(7947, 15894);
}

// REPEAT 4 - TIME: 36.4228348 s

method {:test} Test12() {
expect 979 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(979);
expect r0 == fib(979);
}
method {:test} Test13() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(6);
expect r0 == fact(6);
}
method {:test} Test14() {
expect 7948 > 0 && 23616 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(7948, 23616);
expect r0 == gcd(7948, 23616);
}

// REPEAT 5 - TIME: 45.2666838 s

method {:test} Test15() {
expect 980 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(980);
expect r0 == fib(980);
}
method {:test} Test16() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(7);
expect r0 == fact(7);
}
method {:test} Test17() {
expect 19528 > 0 && 39056 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(19528, 39056);
expect r0 == gcd(19528, 39056);
}

// REPEAT 6 - TIME: 55.6032368 s

method {:test} Test18() {
expect 981 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(981);
expect r0 == fib(981);
}
method {:test} Test19() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(8);
expect r0 == fact(8);
}
method {:test} Test20() {
expect 19529 > 0 && 39058 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(19529, 39058);
expect r0 == gcd(19529, 39058);
}

// REPEAT 7 - TIME: 67.0657738 s

method {:test} Test21() {
expect 982 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(982);
expect r0 == fib(982);
}
method {:test} Test22() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(9);
expect r0 == fact(9);
}
method {:test} Test23() {
expect 19530 > 0 && 46780 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(19530, 46780);
expect r0 == gcd(19530, 46780);
}

// REPEAT 8 - TIME: 80.0218125 s

method {:test} Test24() {
expect 983 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(983);
expect r0 == fib(983);
}
method {:test} Test25() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(10);
expect r0 == fact(10);
}
method {:test} Test26() {
expect 19531 > 0 && 46781 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(19531, 46781);
expect r0 == gcd(19531, 46781);
}

// REPEAT 9 - TIME: 93.1559401 s

method {:test} Test27() {
expect 984 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(984);
expect r0 == fib(984);
}
method {:test} Test28() {
expect 11 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(11);
expect r0 == fact(11);
}
method {:test} Test29() {
expect 31110 > 0 && 62220 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(31110, 62220);
expect r0 == gcd(31110, 62220);
}

// REPEAT 10 - TIME: 105.1133104 s
