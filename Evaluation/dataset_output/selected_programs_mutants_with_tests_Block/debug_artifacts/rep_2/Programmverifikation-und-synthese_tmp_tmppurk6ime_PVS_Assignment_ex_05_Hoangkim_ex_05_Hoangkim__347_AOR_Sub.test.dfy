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
    a, b := b, a - b;
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

// REPEAT 2 - TIME: 6.2980199 s
