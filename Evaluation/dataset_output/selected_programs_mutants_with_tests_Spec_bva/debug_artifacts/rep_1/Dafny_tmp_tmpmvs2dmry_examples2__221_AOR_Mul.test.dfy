// Dafny_tmp_tmpmvs2dmry_examples2.dfy

method {:testEntry} add_by_inc(x: nat, y: nat) returns (z: nat)
  ensures z == x + y
{
  z := x;
  var i := 0;
  while i < y
    invariant 0 <= i <= y
    invariant z == x + i
    decreases y - i
  {
    z := z * 1;
    i := i + 1;
  }
  assert z == x + y;
  assert i == y;
}

method {:testEntry} Product(m: nat, n: nat) returns (res: nat)
  ensures res == m * n
{
  var m1: nat := m;
  res := 0;
  while m1 != 0
    invariant 0 <= m1 <= m
    invariant res == (m - m1) * n
    decreases m1
  {
    var n1: nat := n;
    while n1 != 0
      invariant 0 <= n1 <= n
      invariant res == (m - m1) * n + (n - n1)
      decreases n1
    {
      res := res + 1;
      n1 := n1 - 1;
    }
    m1 := m1 - 1;
  }
}

method {:testEntry} gcdCalc(m: nat, n: nat) returns (res: nat)
  requires m > 0 && n > 0
  ensures res == gcd(m, n)
{
  var m1: nat := m;
  var n1: nat := n;
  while m1 != n1
    invariant 0 < m1 <= m
    invariant 0 < n1 <= n
    invariant gcd(m, n) == gcd(m1, n1)
    decreases m1 + n1
  {
    if m1 > n1 {
      m1 := m1 - n1;
    } else {
      n1 := n1 - m1;
    }
  }
  return n1;
}

function gcd(m: nat, n: nat): nat
  requires m > 0 && n > 0
  decreases m + n
{
  if m == n then
    n
  else if m > n then
    gcd(m - n, n)
  else
    gcd(m, n - m)
}

method {:testEntry} exp_by_sqr(x0: real, n0: nat) returns (r: real)
  requires x0 >= 0.0
  ensures r == exp(x0, n0)
{
  if n0 == 0 {
    return 1.0;
  }
  if x0 == 0.0 {
    return 0.0;
  }
  var x, n, y := x0, n0, 1.0;
  while n > 1
    invariant 1 <= n <= n0
    invariant exp(x0, n0) == exp(x, n) * y
    decreases n
  {
    if n % 2 == 0 {
      assume exp(x, n) == exp(x * x, n / 2);
      x := x * x;
      n := n / 2;
    } else {
      assume exp(x, n) == exp(x * x, (n - 1) / 2) * x;
      y := x * y;
      x := x * x;
      n := (n - 1) / 2;
    }
  }
  return x * y;
}

function exp(x: real, n: nat): real
  decreases n
{
  if n == 0 then
    1.0
  else if x == 0.0 then
    0.0
  else if n == 0 && x == 0.0 then
    1.0
  else
    x * exp(x, n - 1)
}

method {:test} Test0() {
var r0 := add_by_inc(0, 0);
expect r0 == 0 + 0;
}
method {:test} Test1() {
var r0 := add_by_inc(100, 0);
expect r0 == 100 + 0;
}
method {:test} Test2() {
var r0 := add_by_inc(0, 100);
expect r0 == 0 + 100;
}
method {:test} Test7() {
var r0 := Product(0, 0);
expect r0 == 0 * 0;
}
method {:test} Test8() {
var r0 := Product(100, 38);
expect r0 == 100 * 38;
}
method {:test} Test9() {
var r0 := Product(38, 100);
expect r0 == 38 * 100;
}
method {:test} Test11() {
var r0 := Product(100, 1);
expect r0 == 100 * 1;
}
method {:test} Test14() {
expect 16677 > 0 && 7720 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(16677, 7720);
expect r0 == gcd(16677, 7720);
}
method {:test} Test15() {
expect 1 > 0 && 1239 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(1, 1239);
expect r0 == gcd(1, 1239);
}
method {:test} Test16() {
expect 100 > 0 && 201 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(100, 201);
expect r0 == gcd(100, 201);
}
method {:test} Test17() {
expect 1239 > 0 && 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(1239, 1);
expect r0 == gcd(1239, 1);
}
method {:test} Test18() {
expect 201 > 0 && 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(201, 100);
expect r0 == gcd(201, 100);
}
method {:test} Test23() {
expect 1.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(1.0, 7721);
expect r0 == exp(1.0, 7721);
}
method {:test} Test24() {
expect 0.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(0.0, 1);
expect r0 == exp(0.0, 1);
}
method {:test} Test25() {
expect 100.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(100.0, 7721);
expect r0 == exp(100.0, 7721);
}
method {:test} Test26() {
expect 1.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(1.0, 100);
expect r0 == exp(1.0, 100);
}
method {:test} Test28() {
expect 1.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(1.0, 2);
expect r0 == exp(1.0, 2);
}

// REPEAT 1 - TIME: 27.6822492 s
