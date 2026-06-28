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

method {:test} Test11() {
var r0 := add_by_inc(1, 1);
expect r0 == 1 + 1;
}
method {:test} Test12() {
var r0 := Product(2, 1);
expect r0 == 2 * 1;
}
method {:test} Test14() {
expect 18757 > 0 && 4951 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(18757, 4951);
expect r0 == gcd(18757, 4951);
}
method {:test} Test17() {
expect 39.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(39.0, 1239);
expect r0 == exp(39.0, 1239);
}

// REPEAT 2 - TIME: 11.4237016 s

method {:test} Test20() {
var r0 := add_by_inc(2, 2);
expect r0 == 2 + 2;
}
method {:test} Test21() {
var r0 := Product(3, 2);
expect r0 == 3 * 2;
}
method {:test} Test23() {
expect 18758 > 0 && 4952 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(18758, 4952);
expect r0 == gcd(18758, 4952);
}
method {:test} Test26() {
expect 79.0/2.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(79.0/2.0, 1240);
expect r0 == exp(79.0/2.0, 1240);
}

// REPEAT 3 - TIME: 15.3190775 s

method {:test} Test29() {
var r0 := add_by_inc(3, 3);
expect r0 == 3 + 3;
}
method {:test} Test30() {
var r0 := Product(4, 3);
expect r0 == 4 * 3;
}
method {:test} Test32() {
expect 18759 > 0 && 4953 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(18759, 4953);
expect r0 == gcd(18759, 4953);
}
method {:test} Test35() {
expect 40.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(40.0, 1241);
expect r0 == exp(40.0, 1241);
}

// REPEAT 4 - TIME: 19.3503112 s

method {:test} Test38() {
var r0 := add_by_inc(4, 4);
expect r0 == 4 + 4;
}
method {:test} Test39() {
var r0 := Product(5, 4);
expect r0 == 5 * 4;
}
method {:test} Test41() {
expect 18760 > 0 && 4954 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(18760, 4954);
expect r0 == gcd(18760, 4954);
}
method {:test} Test44() {
expect 81.0/2.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(81.0/2.0, 1242);
expect r0 == exp(81.0/2.0, 1242);
}

// REPEAT 5 - TIME: 23.0654721 s

method {:test} Test47() {
var r0 := add_by_inc(5, 5);
expect r0 == 5 + 5;
}
method {:test} Test48() {
var r0 := Product(27, 5);
expect r0 == 27 * 5;
}
method {:test} Test50() {
expect 18761 > 0 && 4955 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(18761, 4955);
expect r0 == gcd(18761, 4955);
}
method {:test} Test53() {
expect 41.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(41.0, 1243);
expect r0 == exp(41.0, 1243);
}

// REPEAT 6 - TIME: 26.6702229 s

method {:test} Test56() {
var r0 := add_by_inc(6, 6);
expect r0 == 6 + 6;
}
method {:test} Test57() {
var r0 := Product(28, 6);
expect r0 == 28 * 6;
}
method {:test} Test59() {
expect 18762 > 0 && 4956 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(18762, 4956);
expect r0 == gcd(18762, 4956);
}
method {:test} Test62() {
expect 83.0/2.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(83.0/2.0, 1244);
expect r0 == exp(83.0/2.0, 1244);
}

// REPEAT 7 - TIME: 31.1840217 s

method {:test} Test65() {
var r0 := add_by_inc(7, 7);
expect r0 == 7 + 7;
}
method {:test} Test66() {
var r0 := Product(29, 8952);
expect r0 == 29 * 8952;
}
method {:test} Test67() {
var r0 := Product(29, 7);
expect r0 == 29 * 7;
}
method {:test} Test68() {
expect 18763 > 0 && 4957 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(18763, 4957);
expect r0 == gcd(18763, 4957);
}
method {:test} Test71() {
expect 42.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(42.0, 1245);
expect r0 == exp(42.0, 1245);
}

// REPEAT 8 - TIME: 34.9024887 s

method {:test} Test74() {
var r0 := add_by_inc(8, 8);
expect r0 == 8 + 8;
}
method {:test} Test75() {
var r0 := Product(30, 8953);
expect r0 == 30 * 8953;
}
method {:test} Test77() {
expect 18764 > 0 && 4958 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(18764, 4958);
expect r0 == gcd(18764, 4958);
}
method {:test} Test80() {
expect 85.0/2.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(85.0/2.0, 1246);
expect r0 == exp(85.0/2.0, 1246);
}

// REPEAT 9 - TIME: 39.0903614 s

method {:test} Test83() {
var r0 := add_by_inc(9, 9);
expect r0 == 9 + 9;
}
method {:test} Test84() {
var r0 := Product(31, 8954);
expect r0 == 31 * 8954;
}
method {:test} Test86() {
expect 18765 > 0 && 4959 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(18765, 4959);
expect r0 == gcd(18765, 4959);
}
method {:test} Test89() {
expect 43.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(43.0, 1247);
expect r0 == exp(43.0, 1247);
}

// REPEAT 10 - TIME: 43.42588 s
