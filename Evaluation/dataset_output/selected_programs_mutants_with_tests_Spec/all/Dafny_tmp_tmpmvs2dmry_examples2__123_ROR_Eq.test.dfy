// Dafny_tmp_tmpmvs2dmry_examples2.dfy

method {:testEntry} add_by_inc(x: nat, y: nat) returns (z: nat)
  ensures z == x + y
{
  z := x;
  var i := 0;
  while i == y
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
var r0 := Product(0, 0);
expect r0 == 0 * 0;
}
method {:test} Test2() {
expect 16677 > 0 && 7720 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(16677, 7720);
expect r0 == gcd(16677, 7720);
}
method {:test} Test3() {
expect 1.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(1.0, 7721);
expect r0 == exp(1.0, 7721);
}

// REPEAT 1 - TIME: 5.2307301 s

method {:test} Test4() {
var r0 := add_by_inc(1, 1);
expect r0 == 1 + 1;
}
method {:test} Test5() {
var r0 := Product(1, 1);
expect r0 == 1 * 1;
}
method {:test} Test6() {
expect 16678 > 0 && 7721 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(16678, 7721);
expect r0 == gcd(16678, 7721);
}
method {:test} Test7() {
expect 2.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(2.0, 7722);
expect r0 == exp(2.0, 7722);
}

// REPEAT 2 - TIME: 8.0238023 s

method {:test} Test8() {
var r0 := add_by_inc(2, 2);
expect r0 == 2 + 2;
}
method {:test} Test9() {
var r0 := Product(2, 2);
expect r0 == 2 * 2;
}
method {:test} Test10() {
expect 16679 > 0 && 7722 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(16679, 7722);
expect r0 == gcd(16679, 7722);
}
method {:test} Test11() {
expect 3.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(3.0, 7723);
expect r0 == exp(3.0, 7723);
}

// REPEAT 3 - TIME: 10.8806123 s

method {:test} Test12() {
var r0 := add_by_inc(3, 3);
expect r0 == 3 + 3;
}
method {:test} Test13() {
var r0 := Product(3, 3);
expect r0 == 3 * 3;
}
method {:test} Test14() {
expect 16680 > 0 && 7723 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(16680, 7723);
expect r0 == gcd(16680, 7723);
}
method {:test} Test15() {
expect 4.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(4.0, 7724);
expect r0 == exp(4.0, 7724);
}

// REPEAT 4 - TIME: 12.9149549 s

method {:test} Test16() {
var r0 := add_by_inc(4, 4);
expect r0 == 4 + 4;
}
method {:test} Test17() {
var r0 := Product(4, 4);
expect r0 == 4 * 4;
}
method {:test} Test18() {
expect 16681 > 0 && 7724 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(16681, 7724);
expect r0 == gcd(16681, 7724);
}
method {:test} Test19() {
expect 5.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(5.0, 7725);
expect r0 == exp(5.0, 7725);
}

// REPEAT 5 - TIME: 14.7626433 s

method {:test} Test20() {
var r0 := add_by_inc(5, 5);
expect r0 == 5 + 5;
}
method {:test} Test21() {
var r0 := Product(5, 5);
expect r0 == 5 * 5;
}
method {:test} Test22() {
expect 16682 > 0 && 7725 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(16682, 7725);
expect r0 == gcd(16682, 7725);
}
method {:test} Test23() {
expect 6.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(6.0, 7726);
expect r0 == exp(6.0, 7726);
}

// REPEAT 6 - TIME: 16.5476074 s

method {:test} Test24() {
var r0 := add_by_inc(6, 6);
expect r0 == 6 + 6;
}
method {:test} Test25() {
var r0 := Product(6, 6);
expect r0 == 6 * 6;
}
method {:test} Test26() {
expect 16683 > 0 && 7726 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(16683, 7726);
expect r0 == gcd(16683, 7726);
}
method {:test} Test27() {
expect 7.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(7.0, 7727);
expect r0 == exp(7.0, 7727);
}

// REPEAT 7 - TIME: 18.2891918 s

method {:test} Test28() {
var r0 := add_by_inc(7, 7);
expect r0 == 7 + 7;
}
method {:test} Test29() {
var r0 := Product(7, 7);
expect r0 == 7 * 7;
}
method {:test} Test30() {
expect 16684 > 0 && 7727 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(16684, 7727);
expect r0 == gcd(16684, 7727);
}
method {:test} Test31() {
expect 8.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(8.0, 7728);
expect r0 == exp(8.0, 7728);
}

// REPEAT 8 - TIME: 20.3537542 s

method {:test} Test32() {
var r0 := add_by_inc(8, 8);
expect r0 == 8 + 8;
}
method {:test} Test33() {
var r0 := Product(8, 8);
expect r0 == 8 * 8;
}
method {:test} Test34() {
expect 16685 > 0 && 7728 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(16685, 7728);
expect r0 == gcd(16685, 7728);
}
method {:test} Test35() {
expect 9.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(9.0, 7729);
expect r0 == exp(9.0, 7729);
}

// REPEAT 9 - TIME: 22.2710182 s

method {:test} Test36() {
var r0 := add_by_inc(9, 9);
expect r0 == 9 + 9;
}
method {:test} Test37() {
var r0 := Product(9, 9);
expect r0 == 9 * 9;
}
method {:test} Test38() {
expect 16686 > 0 && 7729 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(16686, 7729);
expect r0 == gcd(16686, 7729);
}
method {:test} Test39() {
expect 10.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(10.0, 7730);
expect r0 == exp(10.0, 7730);
}

// REPEAT 10 - TIME: 24.1361336 s
