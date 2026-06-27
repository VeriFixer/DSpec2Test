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
  while k <= 0
    invariant sum(n) == x + y * sum(k)
    invariant 0 <= k <= n
    decreases k
  {
    assert sum(n) == x + y * sum(k);
    assert sum(n) == x + y * (k + sum(k - 1));
    assert sum(n) == x + y * k + y * sum(k - 1);
    x := x + y * k;
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

// REPEAT 1 - TIME: 2.612923 s

method {:test} Test1() {
var r0 := Sum(7722);
}

// REPEAT 2 - TIME: 3.713984 s

method {:test} Test2() {
var r0 := Sum(7723);
}

// REPEAT 3 - TIME: 4.8384684 s

method {:test} Test3() {
var r0 := Sum(7724);
}

// REPEAT 4 - TIME: 5.9535057 s

method {:test} Test4() {
var r0 := Sum(7725);
}

// REPEAT 5 - TIME: 7.0030265 s

method {:test} Test5() {
var r0 := Sum(7726);
}

// REPEAT 6 - TIME: 8.0863514 s

method {:test} Test6() {
var r0 := Sum(7727);
}

// REPEAT 7 - TIME: 9.0548316 s

method {:test} Test7() {
var r0 := Sum(7728);
}

// REPEAT 8 - TIME: 9.9737011 s

method {:test} Test8() {
var r0 := Sum(7729);
}

// REPEAT 9 - TIME: 10.7720735 s

method {:test} Test9() {
var r0 := Sum(7730);
}

// REPEAT 10 - TIME: 11.5516158 s
