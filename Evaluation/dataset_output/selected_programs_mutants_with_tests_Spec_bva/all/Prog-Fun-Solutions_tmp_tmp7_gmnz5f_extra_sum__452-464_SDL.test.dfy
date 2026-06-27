// Prog-Fun-Solutions_tmp_tmp7_gmnz5f_extra_sum.dfy

ghost function sum(n: nat): int
{
  if n == 0 then
    0
  else
    n + sum(n - 1)
}

method {:testEntry} Sum(n: nat) returns (s: int)
  ensures s == sum(n)
{
  var x: nat := 0;
  var y: nat := 1;
  var k: nat := n;
  while k > 0
    invariant sum(n) == x + y * sum(k)
    invariant 0 <= k <= n
    decreases k
  {
    assert sum(n) == x + y * sum(k);
    assert sum(n) == x + y * (k + sum(k - 1));
    assert sum(n) == x + y * k + y * sum(k - 1);
    assert sum(n) == x + y * sum(k - 1);
    assert sum(n) == x + y * sum(k - 1);
    k := k - 1;
    assert sum(n) == x + y * sum(k);
  }
  assert k == 0;
  assert sum(n) == x + y * sum(0);
  assert sum(n) == x + y * 0;
  s := x;
  assert sum(n) == s;
}


method {:test} Test0() {
var r0 := Sum(7721);
}
method {:test} Test1() {
var r0 := Sum(100);
}

// REPEAT 1 - TIME: 6.2489795 s

method {:test} Test7() {
var r0 := Sum(7722);
}

// REPEAT 2 - TIME: 7.08505 s

method {:test} Test8() {
var r0 := Sum(7723);
}

// REPEAT 3 - TIME: 7.7958503 s

method {:test} Test9() {
var r0 := Sum(7724);
}

// REPEAT 4 - TIME: 8.4921626 s

method {:test} Test10() {
var r0 := Sum(7725);
}

// REPEAT 5 - TIME: 9.1153332 s

method {:test} Test11() {
var r0 := Sum(7726);
}

// REPEAT 6 - TIME: 9.7687254 s

method {:test} Test12() {
var r0 := Sum(7727);
}

// REPEAT 7 - TIME: 10.3555227 s

method {:test} Test13() {
var r0 := Sum(7728);
}

// REPEAT 8 - TIME: 10.9555357 s

method {:test} Test14() {
var r0 := Sum(7729);
}

// REPEAT 9 - TIME: 11.5017695 s

method {:test} Test15() {
var r0 := Sum(7730);
}

// REPEAT 10 - TIME: 12.1236009 s
