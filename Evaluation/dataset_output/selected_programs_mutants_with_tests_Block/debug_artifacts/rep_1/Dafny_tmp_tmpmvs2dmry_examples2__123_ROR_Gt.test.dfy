// Dafny_tmp_tmpmvs2dmry_examples2.dfy

method {:testEntry} add_by_inc(x: nat, y: nat) returns (z: nat)
  ensures z == x + y
{
  z := x;
  var i := 0;
  while i > y
    invariant 0 <= i <= y
    invariant z == x + i
    decreases y - i
  {
    z := z + 1;
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
var r0 := Product(1, 0);
expect r0 == 1 * 0;
}
method {:test} Test3() {
expect 7798 > 0 && 39 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(7798, 39);
expect r0 == gcd(7798, 39);
}
method {:test} Test4() {
expect 18756 > 0 && 4950 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(18756, 4950);
expect r0 == gcd(18756, 4950);
}
method {:test} Test5() {
expect 6673 > 0 && 2438 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(6673, 2438);
expect r0 == gcd(6673, 2438);
}
method {:test} Test6() {
expect 77.0/2.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(77.0/2.0, 1238);
expect r0 == exp(77.0/2.0, 1238);
}
method {:test} Test7() {
expect 1.0/2.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(1.0/2.0, 3);
expect r0 == exp(1.0/2.0, 3);
}
method {:test} Test8() {
expect 1.0/2.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(1.0/2.0, 2);
expect r0 == exp(1.0/2.0, 2);
}
method {:test} Test9() {
expect 0.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(0.0, 1);
expect r0 == exp(0.0, 1);
}
method {:test} Test10() {
expect 0.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(0.0, 0);
expect r0 == exp(0.0, 0);
}

// REPEAT 1 - TIME: 6.7671733 s
