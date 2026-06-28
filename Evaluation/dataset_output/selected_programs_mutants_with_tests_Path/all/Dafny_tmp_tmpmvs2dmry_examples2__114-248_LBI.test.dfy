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
    break;
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
expect 7798 > 0 && 39 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(7798, 39);
expect r0 == gcd(7798, 39);
}
method {:test} Test3() {
expect 0.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(0.0, 0);
expect r0 == exp(0.0, 0);
}
method {:test} Test4() {
expect 0.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(0.0, 1);
expect r0 == exp(0.0, 1);
}
method {:test} Test5() {
expect 77.0/2.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(77.0/2.0, 1238);
expect r0 == exp(77.0/2.0, 1238);
}

// REPEAT 1 - TIME: 49.1907992 s

method {:test} Test6() {
var r0 := add_by_inc(1, 1);
expect r0 == 1 + 1;
}
method {:test} Test7() {
var r0 := Product(1, 1);
expect r0 == 1 * 1;
}
method {:test} Test8() {
expect 7799 > 0 && 40 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(7799, 40);
expect r0 == gcd(7799, 40);
}
method {:test} Test9() {
expect 39.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(39.0, 1239);
expect r0 == exp(39.0, 1239);
}

// REPEAT 2 - TIME: 106.6615828 s

method {:test} Test10() {
var r0 := add_by_inc(2, 2);
expect r0 == 2 + 2;
}
method {:test} Test11() {
var r0 := Product(2, 2);
expect r0 == 2 * 2;
}
method {:test} Test12() {
expect 7800 > 0 && 41 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(7800, 41);
expect r0 == gcd(7800, 41);
}
method {:test} Test13() {
expect 79.0/2.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(79.0/2.0, 1240);
expect r0 == exp(79.0/2.0, 1240);
}

// REPEAT 3 - TIME: 179.4361471 s

method {:test} Test14() {
var r0 := add_by_inc(3, 3);
expect r0 == 3 + 3;
}
method {:test} Test15() {
var r0 := Product(3, 3);
expect r0 == 3 * 3;
}
method {:test} Test16() {
expect 7801 > 0 && 42 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(7801, 42);
expect r0 == gcd(7801, 42);
}
method {:test} Test17() {
expect 40.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(40.0, 1241);
expect r0 == exp(40.0, 1241);
}

// REPEAT 4 - TIME: 279.8978168 s

method {:test} Test18() {
var r0 := add_by_inc(4, 4);
expect r0 == 4 + 4;
}
method {:test} Test19() {
var r0 := Product(4, 4);
expect r0 == 4 * 4;
}
method {:test} Test20() {
expect 7802 > 0 && 43 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(7802, 43);
expect r0 == gcd(7802, 43);
}
method {:test} Test21() {
expect 81.0/2.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(81.0/2.0, 1242);
expect r0 == exp(81.0/2.0, 1242);
}

// REPEAT 5 - TIME: 393.4023816 s

method {:test} Test22() {
var r0 := add_by_inc(5, 5);
expect r0 == 5 + 5;
}
method {:test} Test23() {
var r0 := Product(5, 5);
expect r0 == 5 * 5;
}
method {:test} Test24() {
expect 7803 > 0 && 44 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(7803, 44);
expect r0 == gcd(7803, 44);
}
method {:test} Test25() {
expect 41.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(41.0, 1243);
expect r0 == exp(41.0, 1243);
}

// REPEAT 6 - TIME: 517.6758972 s

method {:test} Test26() {
var r0 := add_by_inc(6, 6);
expect r0 == 6 + 6;
}
method {:test} Test27() {
var r0 := Product(6, 6);
expect r0 == 6 * 6;
}
method {:test} Test28() {
expect 7804 > 0 && 45 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(7804, 45);
expect r0 == gcd(7804, 45);
}
method {:test} Test29() {
expect 83.0/2.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(83.0/2.0, 1244);
expect r0 == exp(83.0/2.0, 1244);
}

// REPEAT 7 - TIME: 685.1563167 s

method {:test} Test30() {
var r0 := add_by_inc(7, 7);
expect r0 == 7 + 7;
}
method {:test} Test31() {
var r0 := Product(7, 7);
expect r0 == 7 * 7;
}
method {:test} Test32() {
expect 7805 > 0 && 46 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(7805, 46);
expect r0 == gcd(7805, 46);
}
method {:test} Test33() {
expect 42.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(42.0, 1245);
expect r0 == exp(42.0, 1245);
}

// REPEAT 8 - TIME: 796.3177429 s

method {:test} Test34() {
var r0 := add_by_inc(8, 8);
expect r0 == 8 + 8;
}
method {:test} Test35() {
var r0 := Product(8, 8);
expect r0 == 8 * 8;
}
method {:test} Test36() {
expect 7806 > 0 && 47 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(7806, 47);
expect r0 == gcd(7806, 47);
}
method {:test} Test37() {
expect 85.0/2.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(85.0/2.0, 1246);
expect r0 == exp(85.0/2.0, 1246);
}

// REPEAT 9 - TIME: 968.1902843 s

method {:test} Test38() {
var r0 := add_by_inc(9, 9);
expect r0 == 9 + 9;
}
method {:test} Test39() {
var r0 := Product(9, 9);
expect r0 == 9 * 9;
}
method {:test} Test40() {
expect 7807 > 0 && 48 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(7807, 48);
expect r0 == gcd(7807, 48);
}
method {:test} Test41() {
expect 43.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(43.0, 1247);
expect r0 == exp(43.0, 1247);
}

// REPEAT 10 - TIME: 1301.5912828 s
