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

method {:test} Test32() {
var r0 := add_by_inc(101, 101);
expect r0 == 101 + 101;
}
method {:test} Test33() {
var r0 := Product(101, 101);
expect r0 == 101 * 101;
}
method {:test} Test34() {
expect 16678 > 0 && 7721 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(16678, 7721);
expect r0 == gcd(16678, 7721);
}
method {:test} Test35() {
expect 101.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(101.0, 7722);
expect r0 == exp(101.0, 7722);
}

// REPEAT 2 - TIME: 30.4062332 s

method {:test} Test36() {
var r0 := add_by_inc(102, 102);
expect r0 == 102 + 102;
}
method {:test} Test37() {
var r0 := Product(102, 102);
expect r0 == 102 * 102;
}
method {:test} Test38() {
expect 16679 > 0 && 7722 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(16679, 7722);
expect r0 == gcd(16679, 7722);
}
method {:test} Test39() {
expect 102.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(102.0, 7723);
expect r0 == exp(102.0, 7723);
}

// REPEAT 3 - TIME: 32.784912 s

method {:test} Test40() {
var r0 := add_by_inc(103, 103);
expect r0 == 103 + 103;
}
method {:test} Test41() {
var r0 := Product(103, 103);
expect r0 == 103 * 103;
}
method {:test} Test42() {
expect 16680 > 0 && 7723 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(16680, 7723);
expect r0 == gcd(16680, 7723);
}
method {:test} Test43() {
expect 103.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(103.0, 7724);
expect r0 == exp(103.0, 7724);
}

// REPEAT 4 - TIME: 35.3470788 s

method {:test} Test44() {
var r0 := add_by_inc(104, 104);
expect r0 == 104 + 104;
}
method {:test} Test45() {
var r0 := Product(104, 104);
expect r0 == 104 * 104;
}
method {:test} Test46() {
expect 16681 > 0 && 7724 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(16681, 7724);
expect r0 == gcd(16681, 7724);
}
method {:test} Test47() {
expect 104.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(104.0, 7725);
expect r0 == exp(104.0, 7725);
}

// REPEAT 5 - TIME: 37.9876014 s

method {:test} Test48() {
var r0 := add_by_inc(105, 105);
expect r0 == 105 + 105;
}
method {:test} Test49() {
var r0 := Product(105, 105);
expect r0 == 105 * 105;
}
method {:test} Test50() {
expect 16682 > 0 && 7725 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(16682, 7725);
expect r0 == gcd(16682, 7725);
}
method {:test} Test51() {
expect 105.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(105.0, 7726);
expect r0 == exp(105.0, 7726);
}

// REPEAT 6 - TIME: 40.3641566 s

method {:test} Test52() {
var r0 := add_by_inc(106, 106);
expect r0 == 106 + 106;
}
method {:test} Test53() {
var r0 := Product(106, 106);
expect r0 == 106 * 106;
}
method {:test} Test54() {
expect 16683 > 0 && 7726 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(16683, 7726);
expect r0 == gcd(16683, 7726);
}
method {:test} Test55() {
expect 106.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(106.0, 7727);
expect r0 == exp(106.0, 7727);
}

// REPEAT 7 - TIME: 42.7089506 s

method {:test} Test56() {
var r0 := add_by_inc(107, 107);
expect r0 == 107 + 107;
}
method {:test} Test57() {
var r0 := Product(107, 107);
expect r0 == 107 * 107;
}
method {:test} Test58() {
expect 16684 > 0 && 7727 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(16684, 7727);
expect r0 == gcd(16684, 7727);
}
method {:test} Test59() {
expect 107.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(107.0, 7728);
expect r0 == exp(107.0, 7728);
}

// REPEAT 8 - TIME: 44.9911956 s

method {:test} Test60() {
var r0 := add_by_inc(108, 108);
expect r0 == 108 + 108;
}
method {:test} Test61() {
var r0 := Product(108, 108);
expect r0 == 108 * 108;
}
method {:test} Test62() {
expect 16685 > 0 && 7728 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(16685, 7728);
expect r0 == gcd(16685, 7728);
}
method {:test} Test63() {
expect 108.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(108.0, 7729);
expect r0 == exp(108.0, 7729);
}

// REPEAT 9 - TIME: 47.7355587 s

method {:test} Test64() {
var r0 := add_by_inc(109, 109);
expect r0 == 109 + 109;
}
method {:test} Test65() {
var r0 := Product(109, 109);
expect r0 == 109 * 109;
}
method {:test} Test66() {
expect 16686 > 0 && 7729 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdCalc(16686, 7729);
expect r0 == gcd(16686, 7729);
}
method {:test} Test67() {
expect 109.0 >= 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := exp_by_sqr(109.0, 7730);
expect r0 == exp(109.0, 7730);
}

// REPEAT 10 - TIME: 50.4595444 s
